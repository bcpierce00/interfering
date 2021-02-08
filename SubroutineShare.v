Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.
Require Import TraceProperties.

(* To introduce sharing, we extend our domain model with two new domains:
   Passed indicates memory that is sealed by a function but explicitly designated
   to allow the immediate callee to access it. Shared indicates memory that has been
   explicitly exempted from the sealing convention; once shared, it cannot be sealed
   until the function activation that shared it has returned.

   Unlike sealing, sharing and passing require compiler input to identify instructions
   that share or pass a location. A typical passing instruction is a write to the end
   of the caller's frame, which will be read as a passed argument by the callee. The
   canonical example of sharing is taking the address of a stack variable without
   proving that the address will not escape. There is then no longer a guarantee that
   it will remain protected.

   Some systems make further guarantees, such as using capabilities to ensure that if
   a pointer escapes, the object in question is only accessed in a memory safe way.
   We regard this as a separate property that might well be enforced in parallel to
   stack safety, but is outside of its scope.
 *)
Section DOMAIN_MODEL.
  
  Inductive StackDomain :=
  | Sealed (d:nat)
  | Shared (d:nat)
  | Passed (d:nat)
  | Unsealed
  | Outside
  .

  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  Variable cdm : CodeMap'. (* Map of where code lives in memory and its annotation. *)
  Variable sm : Addr -> bool. (* Determines whether an address is in the stack. *)
  Variable pOf : MachineState -> PolicyState. (* Policy initialization function. *)

  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Variable sc : SealingConvention.
  
  Definition context : Type := DomainMap * nat.

  (* For the initial context, we construct a domain map that maps the stack to Unsealed
     and everything else to Outside. The stack depth is 0. *)
  Definition initC : context :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Unsealed
                  else Outside
                | _ => Outside
                end in
    (dm, O).
  
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, d) := prev in
    match AnnotationOf cdm (m (Reg PC)) with
    | Some (share f) =>
      let dm' := fun k =>
                   match k with
                   | Mem a =>
                     match f m a, dm k with
                     | Some true, Unsealed => Passed d
                     | Some false, Unsealed => Shared d
                     | _, _ => dm k
                     end
                   | _ => dm k
                   end in
      (dm', d)
    | Some call =>
      let dm' := fun k =>
                    match k, dm k with                      
                    | _, Sealed d => Sealed d (* Fix alll this *)
                    | _, Outside => Outside
                    | Mem a, _ =>
                      if sc m a
                      then Sealed d
                      else Unsealed (* If addresses are marked to be shared but the sealing convention
                                       wants them unsealed, the sealing convention takes precedence *)
                    | _, _ => dm k
                    end in
      (dm', d+1)
    | Some ret => 
      let dm' := fun k =>
                    match dm k with
                    | Sealed d' =>
                      if (d-1) =? d' (* Sealed addresses are unsealed when their sealer is returned to. *)
                      then Unsealed
                      else dm k
                    | Passed d' =>
                      if (d-1) =? d' (* The same is true of passed addresses; they are single-use *)
                      then Unsealed
                      else dm k
                    | Shared d' =>
                      if d =? d' (* But shared addresses persist until the sharer itself returns *)
                      then Unsealed
                      else dm k
                    | _ => dm k
                    end in
      (dm', d-1)
    | _ => (dm, d)
    end.

  (* A component is inaccessible for writes if it is sealed or if it is passed by the a
     function other than the current one, or its immediate caller. *)
  Definition Inaccessible (c:context) (k:Component) : Prop :=
    exists d,
      fst c k = (Sealed d) \/
      (fst c k = (Passed d) /\ d < (snd c)-1).

  (* So we can do ultra eager integrity, like before. *)
  Definition StackIntegrityUE : Prop :=
    forall minit k mcp mcp',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished mcp (finished mcp')) ->
      Inaccessible (cstate mcp) k ->
      mstate mcp k = mstate mcp' k.

  (* The call rule equivalent is identical except for similar changes in scope. *)
  Definition CallRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall mp o m' c' p' MCP',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP -> (* From any state that is a call *)
      AnnotationOf cdm (mcall (Reg PC)) = Some call -> (* As determined by the code annotations *)
      mpstep (mcall,pcall) = Some (mp,o) -> (* That has a successful step, i.e. doesn't immediately fail-stop *)

      (* We can look ahead to the next state whose depth is <= dcall, and take the intervening trace,
         or an infinite trace if there is no such state. *)
      FindSegmentMP updateC (fun m '(dm,d) => d > dcall) mp (updateC mcall (dmcall,dcall)) MCP' ->
      Last MCP' (m',c',p') ->
      (* And that state will maintain the values of all sealed addresses. *)
      forall a,
        sc mcall a = true ->
        mcall (Mem a) = m' (Mem a).      

  (* We can use our nice trace properties (redefined in TraceProperties.v to handle different
     context types) to implement the integrity property. *)
  Definition StackIntegrityEager : Prop :=
    forall minit MCP d,
      FindSegmentMP updateC (fun m c => snd c >= d) (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (Inaccessible (cstate (head MCP))) MCP.

  (* And it ought to imply the call rule. *)
  Theorem EagerIntSufficient :
    StackIntegrityEager ->
    CallRule.
  Proof.
  Admitted.
  
  (* I won't rehash the ultra eager confidentiality here, but move on to the equivalent
     confidentiality rule. We now allow reading of shared memory, and passed by the
     appropriate function. *)
  Definition ConfRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall m p o n MCP' N MO NO,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP -> (* Once again we consider each successful call *)
      AnnotationOf cdm (mcall (Reg PC)) = Some call ->
      mpstep (mcall,pcall) = Some (m,p,o) ->

      (* And take any variant state of the first state within it *)
      variantOf (fun k => dmcall k <> Outside) m n ->
      (* If we trace from both states until they each return... *)
      FindSegmentMP updateC (fun _ '(dm,d) => d = dcall) (m,p) (dmcall,dcall) MCP' ->
      FindSegmentMP updateC (fun _ '(dm,d) => d = dcall) (n,p) (dmcall,dcall) N ->
      (* They should have the same observable behavior *)
      ObsOfMCP MCP' MO ->
      ObsOfMCP N NO ->
      ObsOfMP MO ~=_O ObsOfMP NO /\
      (* And when they return, the states should have changed in identical ways. *)
      (forall m' dm' p',
          Last MCP' (m',(dm',dcall),p') ->
          exists n' dm'',
            Last N (n',(dm'',dcall),p') /\
            sameDifference mcall m' n n').

  Definition StackConfidentialityEager : Prop :=
    forall minit MCP d m dm p,
      let P := (fun m c => snd c >= d) in
      let K := (fun k => Inaccessible (dm,d) k \/ dm k = Unsealed) in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      head MCP = (m,(dm,d),p) ->
      TraceConfidentialityEager updateC K P MCP.

  Theorem EagerConfSufficient :
    StackConfidentialityEager ->
    ConfRule.
  Proof.
  Admitted.

  Definition StackSafety :=
    forall minit MCP m dm d p,
      let P := (fun m '(dm, d') => d' >= d) in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      head MCP = (m,(dm,d),p) ->
      let Ki := (fun k => Inaccessible (dm,d) k) in
      TraceIntegrityEager Ki MCP /\
      let Kc := (fun k => Inaccessible (dm,d) k) in
      TraceConfidentialityEager updateC Kc P MCP.

  Theorem StackSafetySufficient :
    StackSafety ->
    CallRule /\ ConfRule.
  Proof.
  Admitted.

  (* Continued and (for now) concluded in Coroutine.v *)
  
End WITH_MAPS.
