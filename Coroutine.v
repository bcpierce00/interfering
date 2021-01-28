Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.
Require Import TraceProperties.

(* We add coroutines with multiple stacks, defined with static extents (see Machine.v).
   Our domain model uses the same stack domain as previous, but now a top-level domain
   combines a stack identity and the domains of that stack. Outside is now a top domain. *)
Section DOMAIN_MODEL.

  Inductive StackDomain :=
  | Sealed (d:nat)
  | Shared (d:nat)
  | Passed (d:nat)
  | Unsealed
  .

  Inductive TopDomain :=
  | Instack (sid:StackID) (sd:StackDomain)
  | Outside
  .

  Definition DomainMap := Component -> TopDomain.

  (* We will additionally track the depths of all the stack simultaneously. *)
  Definition DepthMap := StackID -> nat.
  Definition initDepM : DepthMap := fun sid => O.
  Definition push (depm: DepthMap) (sid: StackID) :=
    fun sid' => if stack_eqb sid sid'
                then (depm sid)+1
                else depm sid.
  Definition pop (depm: DepthMap) (sid: StackID) :=
    fun sid' => if stack_eqb sid sid'
                then (depm sid)-1
                else depm sid.
  
End DOMAIN_MODEL.

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
  
  Definition StackIntegrityUE : Prop :=
    forall minit k mcp mcp',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished mcp (finished mcp')) ->
      StackInaccessible (cstate mcp) k ->
      mstate mcp k = mstate mcp' k.

  Definition CoroutineIntegrityUE : Prop :=
    forall minit k sid mcp mcp',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished mcp (finished mcp')) ->
      CoroutineInaccessible (cstate mcp) sid k ->
      mstate mcp k = mstate mcp' k.

  (* We can actually do ultra eager confidentiality for coroutines without any more complexity,
     because coroutine properties don't care about allocation. That only comes when subroutine properties
     are layered in. *)
  Definition CoroutineConfidentialityUE : Prop :=
    forall minit sid m c p m' c' p' p'' n n' o o',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished (m,c,p) (finished (m',c',p'))) ->
      variantOf (fun k => CoroutineInaccessible c sid k) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p = p'' /\ o = o'.
  
  Definition StackIntegrityEager : Prop :=
    forall minit MCP d,
      FindSegmentMP updateC (fun m c => snd c = d) (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (StackInaccessible (cstate (head MCP))) MCP.

  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP sid,
      FindSegmentMP updateC (fun m c => activeStack sm m = sid) (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) MCP.
  
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
      SplitInclusive (fun mp2 => sm (ms mp1 (Reg PC)) = sm (ms mp (Reg PC))) (MPTraceOf mp) MPout (MPTraceOf mp2) ->
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

  (* Coming soon: lazy properties. *)

End WITH_MAPS.
