Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.
Require Import TraceProperties.
Require Import Coroutine.

(* A lazy integrity property is one that doesn't care directly about the state
   of the machine, but focuses on whether an adversary can cause changes in the
   visible behavior of another domain. We offer two such properties. The first
   attempts to consider, for any changes to sealed components, a hypothetical
   world in which they do not change.

   The second is slightly stronger, and treats a change to sealed state as a
   secret that should never become observable at all. Its strength avoids certain
   cases where the first property has difficult intuition.
*)
Section LAZY_TRACE_PROPS.
  Variable context : Type.
  Variable updateC : MachineState -> context -> context.

  Definition rollback (m m':MachineState) (K : Component -> Prop) (m'': MachineState) : Prop :=
    forall k,
      K k ->
      m k <> m' k ->
      m'' k = m k /\
      (K k \/ m k = m' k) ->
      m'' k = m' k.

  Definition TraceIntegrityLaziest
             (K : Component -> Prop)
             (MCP:@MCPTrace context) : Prop :=
    forall m c p m' MCP' MCP'' MO MO',
      Last MCP (m,c,p) ->
      rollback m (mstate (head MCP)) K m' ->
      WithContextMP updateC c (MPTraceOf (m,p)) MCP' ->
      WithContextMP updateC c (MPTraceOf (m',p)) MCP'' ->
      ObsOfMCP MCP' MO ->
      ObsOfMCP MCP'' MO' ->
      ObsOfMP MO ~=_O ObsOfMP MO'.

  (* The second property identifies the subset of protected components that
     changed between the beginning and the end of the trace. The property holds
     if that subset remains confidential permanently, defined in terms of trace
     confidentiality holding on the trace from the final state.*)
  Definition TraceIntegrityLazy
             (K : Component -> Prop)
             (MCP:@MCPTrace context) : Prop :=
    forall m c p MCP',
      Last MCP (m,c,p) ->
      let K' := fun k => K k /\ mstate (head MCP) k <> mstate (m,c,p) k in
      let P := fun _ _ => False in
      WithContextMP updateC c (MPTraceOf (m,p)) MCP' ->
      TraceConfidentialityEager updateC K' P MCP'.

  (* Distinguishing example
     f() {
       int x = 0;
       if(x)
         print x;
       else
         print 1;
     }

     g() {
       x = 1 // through arithmetic from the stack pointer, set x to 1
     }
   *)


End LAZY_TRACE_PROPS.

Section WITH_MAPS.

  Variable cdm : CodeMap'.
  Variable sm : StackMap.
  Variable pOf : MachineState -> PolicyState.

  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Variable sc : SealingConvention.

  Definition context : Type := DomainMap * DepthMap.
  
  Definition initC : DomainMap * DepthMap :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  match findStack sm a with
                  | Some sid => Instack sid Unsealed
                  | None => Outside
                  end
                | Reg r => Outside
                end in
    (dm,initDepM).
  
  (* Once again we need an update function for out context. Note that yields don't
     actually change the domain map, as they don't change which addresses belong to which
     stacks. So we still only consider sharing, calls, and returns. *)
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, depm) := prev in
    let sid := activeStack sm m in
    let d := depm sid in
    match AnnotationOf cdm (m (Reg PC)) with
    | Some (share f) =>
      let dm' := fun k =>
                   match k with
                   | Mem a =>
                     match f m a, dm k with
                     | Some true, Instack sid' Unsealed =>
                       if stack_eqb sid sid' 
                       then Instack sid (Passed d)
                       else dm k
                     | Some false, Instack sid' Unsealed =>
                       if stack_eqb sid sid' 
                       then Instack sid (Shared d)
                       else dm k
                     | _, _ => dm k
                     end
                   | _ => dm k
                   end in
      (dm', depm)
    | Some call =>
      let dm' := fun k =>
                    match k, dm k with                      
                    | _, Instack sid' (Sealed d) => Instack sid' (Sealed d)
                    | _, Outside => Outside
                    | Mem a, Instack sid' _ =>
                      if sc m a && stack_eqb sid sid'
                      then Instack sid (Sealed d)
                      else Instack sid Unsealed (* If addresses are marked to be shared but the sealing convention
                                       wants them unsealed, the sealing convention takes precedence *)
                    | _, _ => dm k
                    end in
      (dm', push depm sid)
    | Some ret => 
      let dm' := fun k =>
                    match dm k with
                    | Instack sid' (Sealed d') =>
                      if (d-1 =? d') && stack_eqb sid sid'
                      then Instack sid Unsealed
                      else dm k
                    | Instack sid' (Passed d') =>
                      if (d-1 =? d') && stack_eqb sid sid'
                      then Instack sid Unsealed
                      else dm k
                    | Instack sid' (Shared d') =>
                      if (d =? d') && stack_eqb sid sid'
                      then Instack sid Unsealed
                      else dm k
                    | _ => dm k
                    end in
      (dm', pop depm sid)
    | _ => (dm, depm)
    end.

  Definition StackInaccessible (c:context) (k:Component) : Prop :=
    exists sid d,
      fst c k = Instack sid (Sealed d) \/
      (fst c k = Instack sid (Passed d) /\ d < (snd c sid)-1).

  (* We split up our inaccessibility criterion into stack and coroutine variations.
     The coroutine version takes the active stack, and prohibits accessing other stacks
     except for shared objects. *)
  Definition CoroutineInaccessible (c:context) (sid:StackID) (k:Component) : Prop :=
    forall sid' sd d,
      fst c k = Instack sid' sd ->
      (sid <> sid /\ sd <> Shared d).
  
  (* We presumably want a Yield Rule that is equivalent to the Call Rule. *)
(*  Definition YieldRule : Prop :=
    forall minit MCP sid my cy py mp o m' c' p' MCP',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (my,cy,py) MCP -> (* From any state that is a yield *)
      AnnotationOf cdm (my (Reg PC)) = Some yield -> (* As determined by the code annotations *)
      activeStack sm my = sid -> (* With active stack sid *)
      mpstep (my,py) = Some (mp,o) -> (* That has a successful step, i.e. doesn't immediately fail-stop *)

      (* We can look ahead to the next state whose stack is sid *)
      FindSegmentMP updateC (fun m c => activeStack sm m <> sid) mp (updateC my cy) MCP' ->
      Last MCP' (m',c',p') ->
      (* And that state will maintain the values of all addresses in sid. *)
      forall a sd,
        fst cy (Mem a) = Instack sid sd ->
        my (Mem a) = m' (Mem a).      
*)  
  Definition StackIntegrityEager : Prop :=
    forall minit MCP sid d,
      let P := fun m (c:context) => snd c sid = d in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (StackInaccessible (cstate (head MCP))) MCP.

  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP sid,
      FindSegmentMP updateC (fun m c => activeStack sm m = sid) (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) MCP.

  (* We can do a confidentiality rule similarly *)
  Definition YieldConfRule : Prop :=
    forall minit MCP sid my cy py m p o n MCP' N MO NO,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (my,cy,py) MCP -> (* Once again we consider each successful call *)
      AnnotationOf cdm (my (Reg PC)) = Some yield ->
      mpstep (my,py) = Some (m,p,o) ->

      (* And take any variant state of the first state within it *)
      variantOf (fun k => forall sd, fst cy k <> Instack sid sd) m n ->
      (* If we trace from both states until they each return... *)
      FindSegmentMP updateC (fun m c => activeStack sm m <> sid) (m,p) cy MCP' ->
      FindSegmentMP updateC (fun m c => activeStack sm m <> sid) (n,p) cy N ->
      (* They should have the same observable behavior *)
      ObsOfMCP MCP' MO ->
      ObsOfMCP N NO ->
      ObsOfMP MO ~=_O ObsOfMP NO /\
      (* And when they return, the states should have changed in identical ways. *)
      (forall m' c' p',
          Last MCP' (m',c',p') ->
          exists n' c'',
            Last N (n',c'',p') /\
            sameDifference my m' n n').
  
  Definition StackConfidentialityEager : Prop :=
    forall minit MCP d sid,
      let P := (fun m c => snd c sid = d) in
      let K := (fun k => StackInaccessible (cstate (head MCP)) k \/
                         fst (cstate (head MCP)) k = Instack sid Unsealed) in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      TraceConfidentialityEager updateC K P MCP.

  Definition CoroutineConfidentialityEager : Prop :=
    forall minit MCP sid,
      let P := (fun m c => activeStack sm m = sid) in
      let K := (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      TraceConfidentialityEager updateC K P MCP.

  (* ***** Control Flow Properties ***** *)


  (* Finally, we also need to consider control flow properties. These are included here because
     they don't really change in interesting ways between the different models. *)
  
  Definition ControlSeparation : Prop :=
    forall minit m1 p1 m2 p2 o f1 f2 ann1 ann2,
      InTrace (m1,p1) (MPTraceOf (minit, pOf minit)) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (m1 (Reg PC)) = inFun f1 ann1 ->
      cdm (m2 (Reg PC)) = inFun f2 ann2 ->
      f1 <> f2 ->
      AnnotationOf cdm (m1 (Reg PC)) = Some call \/
      AnnotationOf cdm (m1 (Reg PC)) = Some ret \/
      AnnotationOf cdm (m1 (Reg PC)) = Some yield.

  Definition YieldBackIntegrity : Prop :=
    forall mp mp1 mp2 MPout,
      InTrace mp1 (MPTraceOf mp) ->
      AnnotationOf cdm (ms mp1 (Reg PC)) = Some yield ->
      SplitInclusive (fun mp2 => sm (ms mp1 (Reg SP)) = sm (ms mp (Reg SP))) (MPTraceOf mp) MPout (MPTraceOf mp2) ->
      justRet (ms mp1) (ms mp2).

  Definition ReturnIntegrity : Prop :=
    forall sid d minit MCP m c p m' c' p',
      let P := fun m c => activeStack sm m = sid /\ (snd c) sid >= d in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      head MCP = (m,c,p) ->
      Last MCP (m',c',p') ->
      justRet m m'.

  Variable em:EntryMap.
  
  Definition EntryIntegrity : Prop :=
  forall minit mp1 m2 p2 o,
    InTrace mp1 (MPTraceOf (minit, pOf minit)) ->
    mpstep mp1 = Some (m2,p2,o) ->
    AnnotationOf cdm (ms mp1 (Reg PC)) = Some call ->
    em (m2 (Reg PC)).

  Definition WellBracketedControlFlow  : Prop :=
    ControlSeparation /\
    ReturnIntegrity /\
    YieldBackIntegrity /\
    EntryIntegrity.

  (* Next check out lazy.v for lazy properties *)

End WITH_MAPS.
