Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* To add sharing, we extend our domain model to divide stack frames into addresses that
   have been shared or passed.*)
Section DOMAIN_MODEL.

  (* Let's extend our previous example first with passing. Again we have a stack resulting
     from caller A calling callee B, now with a value v as an argument. The stack looks like this:

                     sp
     -----------------------------------------------
     | A's frame | v | Empty stack..................
     -----------------------------------------------
          a1      a2                a3

     B has access to v and to everything above the stack pointer. But v is inaccessible!
     We could treat it as part of B's frame, and therefore accessible, but that could
     prove tricky with some calling conventions. Instead we label it "passed" and allow
     it to be an exception to the inaccessibility rule.

     Now suppose that B has an array whose address (a3) is taken. B calls a callee C.

                                                 sp
     --------------------------------------------------------
     | A's frame | v | B's frame | arr | B again | Empty.....
     --------------------------------------------------------
          a1      a2               a3

     From C's perspective, a2 is no longer passed - that represented access granted only
     to the immediate callee, B. But a3 is "shared" because its address has been taken, and
     possibly passed (we cannot statically prove that it was not in all cases, so we make no
     guarantees.) It will remain shrared until deallocated on B's return. a1, finally, we term
     "local," and its inaccessibility is respected by all callees.

     Many systems provide some protection to shared data; the natural example
     is a capability system, in which a shared object is accessible only
     to a holder of a valid pointer, defined as one "descended" from the original.
     Our machinery will not track anything as detailed as pointer provenance, and cannot
     distinguish between legal and illegal uses of pointers to shared memory.

     Instead, our protection properties apply only to components that have not been shared.
     Once a component is shared, it is freely accessible, except in the narrow case of passed
     variables. A variable is passed when its address is only taken by the immediate callee,
     of its allocating function, and we assume that the compiler can guarantee that the pointer
     does not escape. This is the case for stack-allocated argument passing between subroutines.
     A passed component should be accessible in the immediate callee, then inaccessible in its
     nested calls.
   *)
  
  Inductive ShareStatus :=
  | Local
  | Shared
  | Passed
  .
  
  Inductive StackDomain :=
  | Inactive (sd:StackDomain) (ss:ShareStatus)
  | Active (ss:ShareStatus)
  | Outside
  .

  Definition statusOf sd :=
    match sd with
    | Inactive _ ss => Some ss
    | Active ss => Some ss
    | Outside => None
    end.

  (* Finally we need a way to map components to the domain they belong to. *)
  Definition DomainMap := Component -> StackDomain.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  Variable cdm : CodeMap'.
  Variable sm : Addr -> bool.
  Variable pOf : MachineState -> PolicyState.
  
  Definition initD : DomainMap * nat :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Active Local
                  else Outside
                | Reg r => Outside
                end in
    (dm,O).
  
  (* Our update function checks an "annotation" on the code being executed.
     Annotations are defined in Machine.v as an alternative to a million different
     maps, and the ones that matter are call, return, yield, and share.

     Annotations are given by the compiler. We assume that the compiler can tell us
     which instructions represent calls, returns, and yields. Shares are more complicated;
     the compiler cannot directly tell us which component(s) are being shared, because sharing
     is often dynamic. What it can do is identify a relation between the machine state
     and the component(s) being shared.
     
     For an example, suppose that a caller is sharing an address as an argument to its callee.
     It executes a store instruction that the compiler identifies as a share; the target of
     the share is the address to which the argument is being stored, held within the appropriate
     register. So, we would relate a given machine state to the contents of the register in that
     state.
     
     This is a much stronger assumption of information from the compiler than we had before!
     We now fully rely on the compiler to recognize returns, for instance. Relating returns
     to the actual program state is the job of control flow property, WBCF.

     Note that yields don't actually change the domain map, as they don't change which
     addresses belong to which stacks. *)
  
  Definition updateD (m:MachineState) (prev:DomainMap*nat) : DomainMap * nat :=
    let '(dm, d) := prev in
    match AnnotationOf cdm (m (Reg PC)) with
    | Some call => (* A call adjusts the domain map by marking the caller's frame "inactive" *)
                   (* and wrapping the remaining stack in a new instance of "active" *)
      let dm' := fun k =>
                   match k, dm k with
                   | _, Outside => Outside
                   | Mem a, Active ss =>
                     if wlt a (m (Reg SP))
                     then Inactive (Active ss) ss
                     else Active ss
                   | Mem a, Inactive sd Passed =>
                     Inactive (Inactive sd Passed) Local
                   | Mem a, Inactive sd ss =>
                     Inactive (Inactive sd ss) ss
                   | _, _ => dm k
                   end in
      (dm', d+1)
    | Some ret => (* A return unwraps the outermost domain of all components in the initial stack *)
      let dm' := fun k =>
                   match dm k with
                   | Inactive sd Passed => Active Local
                   | Inactive sd ss => sd
                   | _ => dm k
                   end in
      (dm', d-1)
    | _ => (dm,d)
    end.

  Definition StackIntegrityUE : Prop :=
    forall minit MCP k sd mcp mcp',
      WithContextMP updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished mcp (finished mcp')) ->
      fst (cstate mcp) k = Inactive sd Local ->
      mstate mcp k = mstate mcp' k.

    (* We can do a similar Ultra Eager style property with confidentiality, and since we're
       not allowing sharing it is straightforward. But some preliminaries on confidentiality.
       Firstly: confidentiality is expressed in terms of "variant" states. A K-variant
       state of m is a state that agrees with m at every component not in the set K. It may also
       agree at some components in K. The intuition is that if the step from a state changes the
       state in the same way as the step from its K-variant, we can't tell from that step what
       value a component in K was, so K is secret. *)
  Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> m k = n k.
  
  (* "Changing the state in the same way" means that any component that changed is
     one trace ends with the same value in the other. *)
  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (m k <> m' k \/ n k <> n' k) ->
      m' k = n' k.
  
  Definition StackConfidentialityUE : Prop :=
    forall minit MCP sd mcp mcp' n n' o,
      WithContextMP updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished mcp (finished mcp')) ->
      variantOf (fun k => fst (cstate mcp) k = Inactive sd Local) (mstate mcp) n ->
      step (mstate mcp) = (mstate mcp', o) ->
      step n = (n',o) /\ sameDifference (mstate mcp) (mstate mcp') n n'.

  Definition FindSegmentMP P mp dm MCP :=
    exists MCP',
      WithContextMP updateD dm (MPTraceOf mp) MCP' /\
      ContextSegment P MCP' MCP.

  Definition FindSegmentM P m dm MC :=
    exists MC',
      WithContextM updateD dm (MTraceOf m) MC' /\
      ContextSegmentM P MC' MC.
  
  Definition StackIntegrityEager : Prop :=
    forall minit MCP d k sd mcp mcp',
      FindSegmentMP  (fun m c => snd c = d) (minit, pOf minit) initD MCP ->
      mcp = head MCP ->
      fst (cstate mcp) k = Inactive sd Local ->
      Last MCP mcp' ->
      mstate mcp k = mstate mcp' k.
  
  Definition Stuck (MCP : @MCPTrace (DomainMap * nat)) : Prop :=
    exists m c p,
      Last MCP (m,c,p) ->
      mpstep (m,p) = None.

  Definition StackConfidentialityEager : Prop :=
    forall minit M MO d sd m dm p n N NO,
      let P := (fun m c => snd c = d) in
      FindSegmentMP P (minit, pOf minit) initD M ->
      head M = (m,(dm,d),p) ->
      variantOf (fun k => dm k = Inactive sd Local) m n ->
      FindSegmentM P n (dm,d) N ->
      ObsOfMCP M MO ->
      ObsOfMC N NO ->
         (* Case 1 *)
      (forall mend dmend pend,
          Last M (mend,dmend,pend) ->
          ~ P mend (dm,d) ->
          exists nend dnend,
            Last N (nend,dnend) /\
            ObsOfMP MO ~=_O ObsOfM NO /\
            sameDifference m mend n nend)
      /\ (* Case 2 *)
      (Infinite M ->
       ObsOfMP MO ~=_O ObsOfM NO)
      /\ (* Case 3 *)
      (Stuck M ->
       ObsOfMP MO <=_O ObsOfM NO).

  Inductive StepsTo : MachineState -> MachineState -> Prop :=
  | isNow : forall m, StepsTo m m
  | stepsTo : forall m1 m2 m' o,
      step m1 = (m',o) ->
      StepsTo m' m2 ->
      StepsTo m1 m2.

  Definition CallRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall,
      WithContextMP updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP ->
      AnnotationOf cdm (mcall (Reg PC)) = Some call ->
         (* Case 1: Divergence (including due to failstop) *)
      (forall MCP' m' dm d p',
          WithContextMP updateD (dmcall,dcall) (MPTraceOf (mcall,pcall)) MCP' ->
          InTrace (m',dm,p') MCP' ->
          d > dcall)
      \/ (* Case 2: Return *)
      (exists m',
          StepsTo mcall m' /\
          (forall k sd,
            dmcall k = Inactive sd Local ->
            mcall k = m' k) /\
          (forall n k,
              variantOf (fun k' => exists sd, dmcall k = Inactive sd Local) mcall n ->
              StepsTo n m')).

  Theorem EagerSufficient :
    StackIntegrityEager ->
    StackConfidentialityEager ->
    CallRule.
  Proof.
  Admitted.

End WITH_MAPS.
