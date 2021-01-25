Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

Section DOMAIN_MODEL.

  (* In general, a domain is a coherent logical division of the state that
     has meaning in one or more of our security properties. Domain models will get
     complicated, but let's start with a simple one: the simple stack.

     Here the state is divided into "Outside" - anything that isn't part of the
     stack - and Claimed and Unclaimed portions of the stack. Claimed portions
     are indexed by an identifier for the activation that has claimed them, namely
     its depth. The Unclaimed portion is singular. *)

  Inductive StackDomain :=
  | Claimed (d:nat)
  | Unclaimed
  | Outside
  .

  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  (* The Code and Stack maps tell us about the initial layout of memory, as determined
     by the compiler. They will help us build our initial DomainMap and identify
     calls and returns in the code, in the form of annotations. *)

  Variable cdm : CodeMap'.
  Variable sm : Addr -> bool.
  Variable pOf : MachineState -> PolicyState. (* Policy initialization function. *)

  (* We will use the machinery defined at the end of Machine.v to extend traces of the
     machine with context that will inform our properties. In this case the context is a
     pair of a DomainMap and a natural number representing the depth of the stack. *)

  Definition context : Type := DomainMap * nat.

  (* For the initial context, we construct a domain map that maps the stack to Accessible
     and everything else to Outside. The stack depth is 0. *)
  Definition initC : context :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Unclaimed
                  else Outside
                | _ => Outside
                end in
    (dm, O).

  (* Our update function checks an "annotation" on the code being executed.
     Annotations are defined in Machine.v, and the ones that matter here are call and return. *)
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, d) := prev in
    match AnnotationOf cdm (m (Reg PC)) with
    | Some call => (* In our calling convention, the caller claims its frame by setting the stack pointer.
                      Then at the instruction that completes a call, everything below the SP that wasn't
                      already claimed becomes Claimed with the current depth. Everything above retains
                      its prior status, presumably Unclaimed. Finally, the current depth is incremented. *)
      let dm' := fun k =>
                    match k, dm k with
                    | _, Outside => Outside
                    | Mem a, sd =>
                      if wlt a (m (Reg SP))
                      then Claimed d
                      else sd
                    | _, _ => Outside
                    end in
      (dm', d+1)
    | Some ret => (* On a return, we decrement the current depth, for a new current depth of
                     d-1. Then d-1 no longer needs to have claimed any memory, so anything it had
                     claimed is returned to the unclaimed pool (i.e., it can adjust the stack pointer
                     to claim more or less memory on its next call.) *)
      let dm' := fun k =>
                    match dm k with
                    | Claimed d' =>
                      if d-1 =? d'
                      then Unclaimed
                      else Claimed d'
                    | _ => dm k
                    end in
      (dm', d-1)
    | _ => (dm, d)
    end.

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
  
  (* Now it's quite simple to define an "ultra eager" integrity property:
     if we run from any initial state, updating the context as above, then
     at any particular state where a component k is in an Claimed domain,
     k has the same value in the following state (if any.) We term this property
     ultra eager because it "checks" at each step that components that are inaccessible
     don't change, the most frequent it is possible to check. *)
  Definition SimpleStackIntegrityUE : Prop :=
    forall minit k d mcp mcp',
      FindSegmentMP (fun _ _ => False) (minit, pOf minit) initC (notfinished mcp (finished mcp')) ->
      fst (cstate mcp) k = Claimed d ->
      mstate mcp k = mstate mcp' k.

  (* Confidentiality is a little more complicated. There are two contexts in which stack data
     should be secret: when it has been claimed by a caller, it should always be secret. And
     when it has not yet been initialized by the current callee, it should be secret until that
     happens. (This means that, for example, returned functions do not leak their data to future
     calls by leaving it behind in memory.)

     The former is easy to do in an Ultra Eager style; the latter requires additional machinery
     to track initialization. Let's focus on just the side of confidentiality that protects
     Claimed memory. Some preliminaries are in order.

     Firstly: confidentiality is expressed in terms of "variant" states. A K-variant
     state of m is a state that agrees with m at every component not in the set K. It may also
     agree at some components in K. The intuition is that if the step from a state changes the
     state in the same way as the step from its K-variant, we can't tell from that step what
     value a component in K was, so K is secret. *)
  Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> m k = n k.
  
  (* Above we say that each step should change the state in the same way regardless of variation;
     this means that any component that changed is one trace ends with the same value in the other. *)
  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (m k <> m' k \/ n k <> n' k) ->
      m' k = n' k.

  (* Once again, we take adjacent pairs of states in the trace from an arbitrary
     start state and check that a property holds between them. In this case, that
     in any K-variant of the first state where K is the set of components that are
     Claimed in that state, the step has the same observable behavior and makes
     the same changes to state. *)
  Definition ClaimedConfidentialityUE : Prop :=
    forall minit m dm d p m' dm' d' p' n o n' p'' o',
      FindSegmentMP (fun _ _ => False) (minit, pOf minit) initC (notfinished (m,(dm,d),p) (finished (m',(dm',d'),p'))) ->
      variantOf (fun k => dm k = Claimed d) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p = p'' /\ o = o'.

  (* Some things to note: we have hypotheses that both (m,p) and (n,p) step. So we do not consider
     variant states in which (n,p) has a policy violation. We also require that the policy states
     match after the step. This might not be necessary.

     Again, we are not protecting uninitialized memory - it will turn out that when we leave behind
     the Ultra Eager properties, that protection will come naturall. *)

  (* For integrity, ultra eager properties are significantly stronger than we actually
     need. In fact, we want to consider lazy policies that allow illegal writes at times
     in the name of efficiency. So we should consider what our actual goal is here - what
     use are these properties? Here is an example of how we might think of a program logic
     call rule that lets us guarantee that from a call point, if execution returns to the
     caller, Claimed components are preserved. *)
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
    forall minit MCP d d' k mcp mcp',
      FindSegmentMP  (fun m c => snd c = d) (minit, pOf minit) initC MCP ->
      mcp = head MCP ->
      fst (cstate mcp) k = Claimed d' ->
      Last MCP mcp' ->
      mstate mcp k = mstate mcp' k.

  Theorem EagerIntSufficient :
    SimpleStackIntegrityEager ->
    CallRule.
  Proof.
  Admitted.
  
  (* We can make a similar argument about confidentiality, though it may be odd to
     think of a confidentiality call rule. We can at least think of the following as
     the "caller's view" of confidentiality: that the behavior of the callee does not
     depend on any of the stack state at the call, whether or not the caller claimed it.
     Since we aren't modeling any sharing of memory yet, this means that the functions
     communicate only through registers. *)
  Definition ConfRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall n MCP' N MO NO,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP ->
      AnnotationOf cdm (mcall (Reg PC)) = Some call ->
      variantOf (fun k => exists d, dmcall k = Claimed d \/ dmcall k = Unclaimed) mcall n ->
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
    forall minit M MO d d' m dm p n N NO,
      let P := (fun m c => snd c = d) in
      FindSegmentMP P (minit, pOf minit) initC M ->
      head M = (m,(dm,d),p) ->
      variantOf (fun k => dm k = Claimed d' \/ dm k = Unclaimed) m n ->
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
      let K := (fun k => exists d, dm k = Claimed d) in
      TraceIntegrityEager K MCP /\
      TraceConfidentialityEager K P MCP.

  Theorem StackSafetySufficient :
    StackSafety ->
    CallRule /\ ConfRule.
  Proof.
  Admitted.

  (* ***** Control Flow Properties ***** *)
  
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
