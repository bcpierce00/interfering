Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* A Domain is an annotation on a component or set of components reflecting its
   relationship to the program state. Domains are nested, so a domain can be subsumed by
   a higher domain, and all of its components with it. For instance, a stack in a coroutine
   system has a domain containing all of the addresses in the stack's range, and the frames
   pushed on the stack each have their own, as described below. *)
Section DOMAIN_MODEL.

  Inductive ShareStatus :=
  | Local
  | Shared
  | Passed
  .
  
  Inductive StackDomain :=
  | Inactive (sd:StackDomain) (ss:ShareStatus)
  | Active (ss:ShareStatus)
  .

  Definition statusOf sd :=
    match sd with
    | Inactive _ ss => ss
    | Active ss => ss
    end.

  Inductive TopDomain :=
  | Instack (sid:StackID) (sd:StackDomain)
  | Other
  .

  (* Finally we need a way to map components to the domain they belong to. *)
  Definition DomainMap := Component -> TopDomain.
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
  
  Definition initD : DomainMap * DepthMap :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  match findStack sm a with
                  | Some sid => Instack sid (Active Local)
                  | None => Other
                  end
                | Reg r => Other
                end in
    (dm,initDepM).
  
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
  
  Definition updateD (m:MachineState) (prev:DomainMap*DepthMap) : DomainMap * DepthMap :=
    let '(dm, depm) := prev in
    match AnnotationOf cdm (m (Reg PC)), findStack sm (m (Reg SP)) with
    | Some call, Some sid => (* A call adjusts the domain map by marking the caller's frame "inactive" *)
                   (* and wrapping the remaining stack in a new instance of "active" *)
      let dm' := fun k =>
                   match k, dm k with
                   | _, Other => Other
                   | Mem a, Instack sid (Active ss) =>
                     if wlt a (m (Reg SP))
                     then Instack sid (Inactive (Active ss) ss)
                     else Instack sid (Active ss)
                   | Mem a, Instack sid (Inactive sd Passed) =>
                     Instack sid (Inactive (Inactive sd Passed) Local)
                   | Mem a, Instack sid (Inactive sd ss) =>
                     Instack sid (Inactive (Inactive sd ss) ss)
                   | _, _ => dm k
                   end in
      (dm', push depm sid)
    | Some ret, Some sid => (* A return unwraps the outermost domain of all components in the initial stack *)
      let dm' := fun k =>
                   match dm k with
                   | Instack sid (Inactive sd Passed) => Instack sid (Active Local)
                   | Instack sid (Inactive sd ss) => Instack sid sd
                   | _ => dm k
                   end in
      (dm', pop depm sid)
    | _,_ => (dm,depm)
    end.

  Definition StackIntegrityUE : Prop :=
    forall minit MCP k sid sd mcp mcp',
      WithContextMP updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished mcp (finished mcp')) ->
      fst (cstate mcp) k = Instack sid (Inactive sd Local) ->
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
    forall minit MCP sid sd mcp mcp' n n' o,
      WithContextMP updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished mcp (finished mcp')) ->
      variantOf (fun k => fst (cstate mcp) k = Instack sid (Inactive sd Local)) (mstate mcp) n ->
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
    forall minit MCP d k sid sd mcp mcp',
      FindSegmentMP  (fun m c => snd c = d) (minit, pOf minit) initD MCP ->
      mcp = head MCP ->
      fst (cstate mcp) k = Instack sid (Inactive sd Local) ->
      Last MCP mcp' ->
      mstate mcp k = mstate mcp' k.
  
  Definition Stuck (MCP : @MCPTrace (DomainMap * DepthMap)) : Prop :=
    exists m c p,
      Last MCP (m,c,p) ->
      mpstep (m,p) = None.

  Definition StackConfidentialityEager : Prop :=
    forall minit M MO d sid sd m dm depm p n N NO,
      let P := (fun m c => snd c sid = d) in
      FindSegmentMP P (minit, pOf minit) initD M ->
      head M = (m,(dm,depm),p) ->
      variantOf (fun k => dm k = Instack sid (Inactive sd Local)) m n ->
      FindSegmentM P n (dm,depm) N ->
      ObsOfMCP M MO ->
      ObsOfMC N NO ->
         (* Case 1 *)
      (forall mend dmend depmend pend,
          Last M (mend,(dmend,depmend),pend) ->
          ~ P mend (dm,depm) ->
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
    forall minit MCP mcall dmcall depmcall pcall sid,
      WithContextMP updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,depmcall),pcall) MCP ->
      AnnotationOf cdm (mcall (Reg PC)) = Some call ->
      findStack sm (mcall (Reg SP)) = Some sid ->
         (* Case 1: Divergence (including due to failstop) *)
      (forall MCP' m' dm d p',
          WithContextMP updateD (dmcall,depmcall) (MPTraceOf (mcall,pcall)) MCP' ->
          InTrace (m',dm,p') MCP' ->
          d > depmcall sid)
      \/ (* Case 2: Return *)
      (exists m',
          StepsTo mcall m' /\
          (forall k sid sd,
            dmcall k = Instack sid (Inactive sd Local) ->
            mcall k = m' k) /\
          (forall n k,
              variantOf (fun k' => exists sid sd, dmcall k = Instack sid (Inactive sd Local)) mcall n ->
              StepsTo n m')).

  Theorem EagerSufficient :
    StackIntegrityEager ->
    StackConfidentialityEager ->
    CallRule.
  Proof.
  Admitted.

End WITH_MAPS.
