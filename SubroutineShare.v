Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

Section DOMAIN_MODEL.

  Inductive ShareStatus :=
  | Local
  | Passed
  | Shared.
  
  Inductive StackDomain :=
  | Claimed (d:nat)
  | Unclaimed
  | Outside
  .

  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> (StackDomain * ShareStatus).
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  Variable cdm : CodeMap'. (* Map of where code lives in memory and its annotation. *)
  Variable sm : Addr -> bool. (* Determines whether an address is in the stack. *)
  Variable pOf : MachineState -> PolicyState. (* Policy initialization function. *)

  (* We will use the machinery defined at the end of Machine.v to extend traces of the
     machine with context that will inform our properties. In this case the context is a
     pair of a Domain Map and a natural number representing the depth of the stack. *)

  Definition context : Type := DomainMap * nat.

  (* For the initial context, we construct a domain map that maps the stack to Accessible
     and everything else to Outside. The stack depth is 0. *)
  Definition initC : context :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then (Unclaimed,Local)
                  else (Outside,Shared)
                | _ => (Outside,Shared)
                end in
    (dm, O).
  
  (* Our update function checks an "annotation" on the code being executed.
     Annotations are defined in Machine.v as an alternative to a million different
     maps, and the ones that matter here are call and return.

     Annotations are given by the compiler. We assume that the compiler can tell us
     which instructions represent calls and returns. *)
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, d) := prev in
    match AnnotationOf cdm (m (Reg PC)) with
    | Some (share f) =>
      let dm' := fun k =>
                   match k with
                   | Mem a =>
                     match f m a, dm k with
                     | Some true, (Unclaimed,Local) => (Unclaimed,Passed)
                     | Some false, (Unclaimed,_) => (Unclaimed,Shared)
                     | _, _ => dm k
                     end
                   | _ => dm k
                   end in
      (dm', d)
    | Some call => (* A call adjusts the domain map by marking the caller's frame "inactive" *)
                   (* and wrapping the remaining stack in a new instance of "active" *)
      let dm' := fun k =>
                    match k, dm k with
                    | _, (Outside,ss) => (Outside,ss)
                    | Mem a, (Unclaimed,ss) =>
                      if wlt a (m (Reg SP))
                      then (Claimed d,ss)
                      else (Unclaimed,Local)
                    | _, _ => dm k
                    end in
      (dm', d+1)
    | Some ret => (* A return unwraps the outermost domain of all components in the initial stack *)
      let dm' := fun k =>
                    match dm k with
                    | (Claimed d', ss) =>
                      if d =? d'
                      then (Unclaimed,Local)
                      else dm k
                    | _ => dm k
                    end in
      (dm', d-1)
    | _ => (dm, d)
    end.

  (* A component is inaccessible if it is claimed and local, or claimed by a
     depth that is buried in the stack. *)
  Definition Inaccessible (c:context) (k:Component) : Prop :=
    exists d,
      fst c k = (Claimed d, Local) \/
      (fst c k = (Claimed d, Passed) /\ d < (snd c)-1).
  
  (* Now it's quite simple to define an "ultra eager" integrity property:
     if we run from any initial state, updating the context as above, then
     at any particular state where a component k is in an Inaccessible domain,
     k has the same value in the following state (if any.) We term this property
     ultra eager because it "checks" at each step that components that are inaccessible
     don't change, the most frequent it is possible to check. *)
  Definition SimpleStackIntegrityUE : Prop :=
    forall minit MCP k mcp mcp',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished mcp (finished mcp')) ->
      Inaccessible (cstate mcp) k ->
      mstate mcp k = mstate mcp' k.

    (* We can do a similar ultra eager style property with confidentiality, and since we're
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

  (* Once again, we take adjacent pairs of states in the trace from an arbitrary
     start state and check that a property holds between them. In this case, that
     in any K-variant of the first state where K is the set of components that are
     Inacessible in that state, the step has the same observable behavior and makes
     the same changes to state. *)
  Definition SimpleStackConfidentialityUE : Prop :=
    forall minit MCP m dm d p m' dm' d' p' n o n' p'' o',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,(dm,d),p) (finished (m',(dm',d'),p'))) ->
      variantOf (fun k => Inaccessible (dm,d) k) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p = p'' /\ o = o'.

  (* Once again, because this doesn't track initialization,
     it doesn't actually fully work for the unclaimed memory. *)

  (* Here are some helper relations to combine the addition of context to a trace,
     and the segmenting of the resulting trace by a proposition P.*)
  Definition FindSegmentMP P mp c MCP :=
    exists MCP',
      WithContextMP updateC c (MPTraceOf mp) MCP' /\
      ContextSegment P MCP' MCP.

  Definition FindSegmentM P m c MC :=
    exists MC',
      WithContextM updateC c (MTraceOf m) MC' /\
      ContextSegmentM P MC' MC.

  (* For integrity, ultra eager properties are significantly stronger than we actually
     need. In fact, we want to consider lazy policies that allow illegal writes at times
     in the name of efficiency. So we should consider what our actual goal is here - what
     use are these properties? Here is an example of how we might think of a program logic
     call rule that lets us guarantee that from a call point, if execution returns to the
     caller, Inaccessible components are preserved. *)
  
  Definition CallRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP ->
      AnnotationOf cdm (mcall (Reg PC)) = Some call ->
         (* Case 1: Divergence (including due to failstop) *)
      (forall MCP' m' dm d p',
          WithContextMP updateC (dmcall,dcall) (MPTraceOf (mcall,pcall)) MCP' ->
          InTrace (m',(dm,d),p') MCP' ->
          d > dcall)
      \/ (* Case 2: Return *)
      (exists mp o m' c' p' MCP',
          mpstep (mcall,pcall) = Some (mp,o) /\
          FindSegmentMP (fun m '(dm,d) => d > dcall) mp (updateC mcall (dmcall,dcall)) MCP' /\
          Last MCP' (m',c',p') /\
          forall a,
            wlt a (mcall (Reg SP)) = true ->
            mcall (Mem a) = m' (Mem a)).

  (* We could use this as our ultimate specification, or just to guide our trace
     properties. Note that this rule cares nothing for what happens to the state of
     the Inaccessible components during the call, only that whe we return, they are
     the same. Our eager property reflects this; instead of guaranteeing that they never
     change, it guarantees that they are unchanged if and when the function returns. *)
  
  Definition SimpleStackIntegrityEager : Prop :=
    forall minit MCP d k mcp mcp',
      FindSegmentMP  (fun m c => snd c = d) (minit, pOf minit) initC MCP ->
      mcp = head MCP ->
      Inaccessible (cstate mcp) k ->
      Last MCP mcp' ->
      mstate mcp k = mstate mcp' k.

  Theorem EagerIntSufficient :
    SimpleStackIntegrityEager ->
    CallRule.
  Proof.
  Admitted.
  
  (* We can make a similar argument about confidentiality, though it may be odd to
     think of a confidentiality call rule. We can at least think of the following as
     the "caller's view" of confidentiality: that from the call to the return, its
     Inaccessible memory ought change nothing about the observable behavior of the
     machine, and if control returns, its Inaccessible memory also did not impact the
     returned state. *)

  Definition ConfRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall n MCP' N MO NO,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP ->
      AnnotationOf cdm (mcall (Reg PC)) = Some call ->
      variantOf (fun k => Inaccessible (dmcall,dcall) k \/ fst (dmcall k) = Unclaimed) mcall n ->
      (* Clause 1: output up to return identical *)
      PrefixUpTo (fun '(_,(dm,d),_) => d = dcall) MCP MCP' ->
      FindSegmentM (fun _ '(dm,d) => d = dcall) n (dmcall,dcall) N ->
      ObsOfMCP MCP' MO ->
      ObsOfMC N NO ->
      ObsOfMP MO ~=_O ObsOfM NO /\
      (* Clause 2: if return, then state changes the same *)
      (forall m' dm' p',
          Last MCP' (m',(dm',dcall),p') ->
          exists n' dm'',
            Last N (n',(dm'',dcall)) /\
            sameDifference mcall m' n n').

  (* The flip side of the caller's rule is the trace property that holds on subtraces
     representing calls. This only needs to be strong enough to support the caller-side
     reasoning, so here is an example of such an eager (but not ultra-eager) property. *)
  Definition SimpleStackConfidentialityEager : Prop :=
    forall minit M MO d m dm p n N NO,
      let P := (fun m c => snd c = d) in
      FindSegmentMP P (minit, pOf minit) initC M ->
      head M = (m,(dm,d),p) ->
      variantOf (fun k => Inaccessible (dm,d) k \/ fst (dm k) = Unclaimed) m n ->
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
      (forall mend dmend pend,
          Last M (mend, dmend, pend) ->
          P mend (dm,d) ->
          ObsOfMP MO <=_O ObsOfM NO).

  Theorem EagerConfSufficient :
    SimpleStackConfidentialityEager ->
    ConfRule.
  Proof.
  Admitted.

  (* Now the above properties do a few things all at once that it helps to disentangle. They
     quantify over all initial states, then over all segments of a trace at or above a certain
     depth on the stack, ending with the return when the depth is reduced. And they state
     properties of those segments. Lets focus on just capturing what it means for a trace
     to respect the integrity and confidentiality of components, and separate out the finding
     of the traces. The predicate K will indicate the set of components that must be protected. *)

  Definition TraceIntegrityEager (K : Component -> Prop) (MCP:MCPTrace) : Prop :=
    forall k (mcp':@MCPState context),
      K k->
      Last MCP mcp' ->
      mstate (head MCP) k = mstate mcp' k.

  (* The confidentiality trace property needs to know when the variant trace can be considered to have
     returned, for which it takes a predicate on states and contexts, P. *)
  Definition TraceConfidentialityEager (K : Component -> Prop)
             (P:MachineState -> context -> Prop)
             (MCP:@MCPTrace context) : Prop :=
    forall MCP MO d m dm p n N NO,
      head MCP = (m,(dm,d),p) ->
      variantOf K m n ->
      FindSegmentM P n (dm,d) N ->
      ObsOfMCP MCP MO ->
      ObsOfMC N NO ->
         (* Case 1 *)
      (forall mend dmend pend,
          Last MCP (mend,dmend,pend) ->
          ~ P mend (dm,d) ->
          exists nend dnend,
            Last N (nend,dnend) /\
            ObsOfMP MO ~=_O ObsOfM NO /\
            sameDifference m mend n nend)
      /\ (* Case 2 *)
      (Infinite MCP ->
       ObsOfMP MO ~=_O ObsOfM NO)
      /\ (* Case 3 *)
      (forall mend dmend pend,
          Last MCP (mend, dmend, pend) ->
          P mend (dm,d) ->
          ObsOfMP MO <=_O ObsOfM NO).

  (* Now we can quantify over all initial states and segments starting with calls,
     to create a property of the system that all calls enjoy both confidentiality and
     integrity. *)
  Definition StackSafety :=
    forall minit MCP m dm d p,
      let P := (fun m '(dm, d') => d' >= d) in
      FindSegmentMP P (minit, pOf minit) initC MCP ->
      head MCP = (m,(dm,d),p) ->
      let K := (fun k => Inaccessible (dm,d) k) in
      TraceIntegrityEager K MCP /\
      TraceConfidentialityEager K P MCP.

  Theorem StackSafetySufficient :
    StackSafety ->
    CallRule /\ ConfRule.
  Proof.
  Admitted.

  (* ***** Control Flow Properties ***** *)
  (* The addition of sharing does not change these. *)
  
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
    forall d minit MCP m c p m' c' p',
      FindSegmentMP (fun m '(dm,d') => d' >= d) (minit, pOf minit) initC MCP ->
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

End WITH_MAPS.
