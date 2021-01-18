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
   a higher domain, and all of its components with it.

   First, an example of stack domains. Suppose we have a stack resulting from caller A
   calling callee B. The stack looks like this:
               sp
   -----------------------------------------------
   | A's frame | Empty stack..................
   -----------------------------------------------
        a1                      a2

   B's frame is not yet allocated until it sets the stack pointer, but B
   has access to everything above the current stack pointer. So lets consider the status of
   addresses a1 and a2 in the moment B gains control.

   a1 is in a frame that is currently inaccessible, but someday - after B returns - will
   again be active. a2 is still in the accessible part of the stack. If B makes another call,
   say to a functin C, we will have:

                            sp
   -----------------------------------------------
   | A's frame | B's frame  | Empty.....
   -----------------------------------------------
        a1        a2

   a1 and a2 are both inaccessible. But a2 will be accessible again on the next return.
   Whereas a1 will be inaccesible still, until the return after (assuming no further calls.)
   So in a stack domain, an Inaccessible domain carries a nested stack domain that is the one
   that will be used after the next unmatched return.
 *)

Section DOMAIN_MODEL.
  (* Outside is non-stack memory and registers. Inaccessible and Accessible are as described above. *)
  Inductive StackDomain :=
  | Inaccessible (sd:StackDomain)
  | Accessible
  | Outside
  .

  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
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
                  then Accessible
                  else Outside
                | _ => Outside
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
    | Some call => (* A call adjusts the domain map by marking the caller's frame "inactive" *)
                   (* and wrapping the remaining stack in a new instance of "active" *)
      let dm' := fun k =>
                    match k, dm k with
                    | _, Outside => Outside
                    | Mem a, sd =>
                      if wlt a (m (Reg SP))
                      then Inaccessible sd
                      else sd
                    | _, _ => Outside
                    end in
      (dm', d+1)
    | Some ret => (* A return unwraps the outermost domain of all components in the initial stack *)
      let dm' := fun k =>
                    match dm k with
                    | Inaccessible sd => sd
                    | _ => dm k
                    end in
      (dm', d-1)
    | _ => (dm, d)
    end.

  (* Now it's quite simple to define an "ultra eager" integrity property:
     if we run from any initial state, updating the context as above, then
     at any particular state where a component k is in an Inaccessible domain,
     k has the same value in the following state (if any.) We term this property
     ultra eager because it "checks" at each step that components that are inaccessible
     don't change, the most frequent it is possible to check. *)
  Definition SimpleStackIntegrityUE : Prop :=
    forall minit MCP k sd mcp mcp',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished mcp (finished mcp')) ->
      fst (cstate mcp) k = Inaccessible sd ->
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
    forall minit MCP sd m dm d p m' dm' d' p' n o n' p'' o',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,(dm,d),p) (finished (m',(dm',d'),p'))) ->
      variantOf (fun k => dm k = Inaccessible sd) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p = p'' /\ o = o'.

  (* Here are some helper relations to combine the addition of context to a trace,
     and the segmenting of the resulting trace by a proposition P.*)
  Definition FindSegmentMP P mp dm MCP :=
    exists MCP',
      WithContextMP updateC dm (MPTraceOf mp) MCP' /\
      ContextSegment P MCP' MCP.

  Definition FindSegmentM P m dm MC :=
    exists MC',
      WithContextM updateC dm (MTraceOf m) MC' /\
      ContextSegmentM P MC' MC.

  (* For integrity, ultra eager properties are significantly stronger than we actually
     need. In fact, we want to consider lazy policies that allow illegal writes at times
     in the name of efficiency. So we should consider what our actual goal is here - what
     use are these properties? Here is an example of how we might think of a program logic
     call rule that lets us guarantee that from a call point, if execution returns to the
     caller, Inaccessible components are preserved. *)
  Inductive StepsTo : MachineState -> MachineState -> Prop :=
  | isNow : forall m, StepsTo m m
  | stepsTo : forall m1 m2 m' o,
      step m1 = (m',o) ->
      StepsTo m' m2 ->
      StepsTo m1 m2.
  
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
      (exists m',
          StepsTo mcall m' /\
          forall k sd,
            dmcall k = Inaccessible sd ->
            mcall k = m' k).

  (* We could use this as our ultimate specification, or just to guide our trace
     properties. Note that this rule cares nothing for what happens to the state of
     the Inaccessible components during the call, only that whe we return, they are
     the same. Our eager property reflects this; instead of guaranteeing that they never
     change, it guarantees that they are unchanged if and when the function returns. *)
  
  Definition SimpleStackIntegrityEager : Prop :=
    forall minit MCP d k sd mcp mcp',
      FindSegmentMP  (fun m c => snd c = d) (minit, pOf minit) initC MCP ->
      mcp = head MCP ->
      fst (cstate mcp) k = Inaccessible sd ->
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
      variantOf (fun k => exists sd, dmcall k = Inaccessible sd) mcall n ->
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
    forall minit M MO d sd m dm p n N NO,
      let P := (fun m c => snd c = d) in
      FindSegmentMP P (minit, pOf minit) initC M ->
      head M = (m,(dm,d),p) ->
      variantOf (fun k => dm k = Inaccessible sd) m n ->
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
      let K := (fun k => exists sd, dm k = Inaccessible sd) in
      TraceIntegrityEager K MCP /\
      TraceConfidentialityEager K P MCP.

  Theorem StackSafetySufficient :
    StackSafety ->
    CallRule /\ ConfRule.
  Proof.
  Admitted.

End WITH_MAPS.
