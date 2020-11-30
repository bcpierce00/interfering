Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* A Domain is a logical unit associated with a collection of components, and can be thought of as the
   owner of a component. Domains are nested, so a domain can belong to a higher domain, and all of its
   components with it. For instance, the stack frame for a caller belongs to the active frame for that
   caller as well as the sealed portion of the stack for its callee, and additionally belongs to the
   domain of that stack as a whole (in a multi-stack system). *)
Section DOMAIN_MODEL.

  (* The smallest domain we treat currently is an object, which currently only
     carries information about whether that object is shared (up-stack).
     A fuller model might also need to identify each object, but we don't actually care right now. *)
  Inductive ObjD :=
  | shared
  | local
  .
  
  (* Next are stack frames. Frame domains are recursive. Consider an initial stack: every address
     in it belongs to the active frame. Then upon a call, there is are two new domains - the "sealed"
     frame of the caller and the active frame of the callee. But an address belonging to either of
     these domains also belongs to the original active frame.

     An active frame domain is subdivided into objects, which may be local or shared. It might be the
     base domain or the child of another (active) frame domain.

     A sealed frame domain *must* be the child of another frame domain, and at some point down the
     stack it will be an active frame domain. Sealed frames are not divided into objects, but at
     times we will look down the stack to when an address is active to determine its object status.
   *)
  Inductive FrameD :=
  | active : ObjD -> option FrameD -> FrameD
  | sealed : FrameD -> FrameD
  .

  (* Finally, the top-level domain type can make a component part of a stack (in which case
     it also needs to know which stack id it belongs to). It can also be code, in the heap, or
     a register. Later we can expand the definition of the heap to extend the model. *)
  Inductive TopD :=
  | stack : StackID -> FrameD -> TopD
  | code
  | heap
  | registers
  .

  Definition DomainMap := Component -> TopD.
  
End DOMAIN_MODEL.

Section WITH_MAPS.
  (* Now we describe how components are assigned to domains with an initial
     domain map and a update function, given our initial program maps *)

  Variable cdm : CodeMap'.
  Variable sm : StackMap.
  Variable pOf : MachineState -> PolicyState.
  
  Definition initD : DomainMap :=
    fun k =>
      match k with
      | Mem a =>
        if isCode' cdm a
        then code
        else match findStack sm a with
             | Some sid => stack sid (active local None)
             | None => heap
             end
      | _ => registers
      end.

  (* Our update function checks the annotation on the code being executed.
     Annotations are defined in Machine.v as an alternative to a million different
     maps, and the ones that matter are call, return, yield, and share.

     Annotations are given by the compiler. We assume that the compiler can tell us
     which instructions represent calls, returns, and yields. Shares are more complicated;
     the compiler cannot tell us which component(s) are being shared. Instead it can identify
     another component, typically a register, that holds the target of the share.

     For example, suppose that a caller is sharing an address as an argument to its callee.
     It executes a store instruction that the compiler identifies as a share; the target of
     the share is the address to which the argument is being stored, held within the appropriate
     register.

     Note that yields don't actually change the contour state, as they don't change which
     addresses belong to which stacks. *)
  Definition updateD (m:MachineState) (dm:DomainMap) :=
    match AnnotationOf cdm (m (Reg PC)) with
    | Some call => (* A call adjusts the domain map by sealing the caller's frame (wrapping it in "sealed") *)
                   (* as well as by wrapping the remaining stack in a new instance of "active" *)
      fun k =>
        match k, dm k with
        | Mem a, stack sid fd =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) && wlt a (m (Reg SP))
          then stack sid (sealed fd)
          else stack sid (active local (Some fd))
        | _,_ => dm k
        end
    | Some ret => (* A return unwraps the outermost domain of all components in the initial stack *)
      fun k =>
        match dm k with
        | stack sid (sealed fd) =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then
            stack sid fd
          else dm k
        | stack sid (active _ (Some fd)) =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then
            stack sid fd
          else dm k
        | _ => dm k
        end
    | Some (share k0) => (* A share applies only to an object in the active frame, and sets it to shared *)
      fun k =>
        match k with
        | Mem a =>
          if weq a (m k0) then
            match dm k with
            | stack sid (active secret fd) => stack sid (active shared fd)
            | _ => dm k
            end
          else dm k
        | _ => dm k
        end
    | _ => dm
    end.

  (* Eventually we will see a unified model of integrity and confidentiality using
     contours, but first we can look at a simple example of how to build a safety property
     on this model: an ad-hoc code safety property. Note that this property gets to be
     simple because the code domain is static; on the way to stack safety we will add
     quite a bit more machinery to deal with changing domains.

     Code safety says that starting from any initial state, between each adjacent
     pair of states mp and mp' in the program trace, all components in the code domain
     are unchanged. *)
  Definition AdHocCodeSafety : Prop :=
    forall minit mp mp' o k,
      InTrace mp (MPTraceOf (minit, pOf minit)) ->
      (initD k) = code ->
      mpstep mp = Some (mp',o) ->
      (ms mp) k = (ms mp') k.  
  
  (* Now suppose that we had, in our formalization, the ability to expand the code
     domain to reflect adding some new code to the system. We might well want such
     a feature some day. We will need to deal with the way domains change over time.
     Let's introduce some machinery for carring extra state along with an MPTrace. *)
  Section WITH_STATE.
    Variable ContextState : Type.
    Variable ContextStateUpdate : MachineState -> ContextState -> ContextState.

    Definition MCPState : Type := MachineState * ContextState * PolicyState.
    Definition MCPTrace := TraceOf MCPState.
    Definition cstate : MCPState -> ContextState := fun '(m,cs,p) => cs.
    Definition MPOTrace := MPTrace'.

      (* WithContour relates an MPTrace to its MCPTrace given an initial contour state cs.
         A finished trace (m,p) is related to (m,cs,p).
         We relate a trace (notfinished (m,p) MP) to (notfinished (m,cs,p) MCP),
         where MP relates to MCP given cs' produced by ContextStateUpdate. Additionally,
         the relation requires that MP begin with m' and p' produced by mpstep (m,p),
         so that only MPTraces produced by the step function relate to any MCPTrace *)
    Inductive WithContext (cs:ContextState) : MPTrace -> MCPTrace -> Prop :=
    | WCFinished : forall m p,
        WithContext cs (finished (m,p)) (finished (m,cs,p))
    | WCNotfinished : forall m p cs' m' p' o MP MCP,
        mpstep (m,p) = Some (m',p',o) ->
        ContextStateUpdate m cs = cs' ->
        WithContext cs' MP MCP ->
        head MP = (m',p') -> (* This checks that MP is actually real *)
        WithContext cs (notfinished (m,p) MP) (notfinished (m,cs,p) MCP).

    (* Similarly, with WithObs we relate an MCPTrace into the MPOTrace
       corresponding to its steps annotated with their observations. We feed
       each step's observation forward, to line up with the machine state that follows that step.
       We will need this later. *)
    Inductive WithObs (o:Observation) : MCPTrace -> MPOTrace -> Prop :=
    | WOFinished : forall m c p,
        WithObs o (finished (m,c,p)) (finished (m,p,o))
    | WONotfinished : forall m c p m' c' o' p' MP MPO,
        WithObs o' MP MPO ->
        mpstep (m,p) = Some ((m',p'),o) ->
        head MP = (m',c',p') ->
        WithObs o (notfinished (m,c,p) MP) (notfinished (m,p,o) MPO).

    (* ObsOfMCP starts the observation with Tau, reflecting that initially
       there is no observation until a step occurs. *)
    Definition ObsOfMCP := WithObs Tau.

      (* ContextSegment relates two MCPTraces given a condition f on machine and context states,
         where the second is a longest subtrace of the first such that f holds on all elements
         except the final. So, it will always have at least two elements, and its head will have been
         preceded by one on which f does not hold, while the last (if any) also does not have f hold.

         We will use this machinery to clip out sections of a trace that we want to check
         against a property, with the final state reflecting the state after some relevant execution.
       *)
    Inductive ContextSegment (f : MachineState -> ContextState -> Prop) : MCPTrace -> MCPTrace -> Prop :=
    | CSCurrent : forall MCP MCP' m cs p,
        head MCP = (m,cs,p) ->
        f m cs ->
        PrefixUpTo (fun '(m,cs,p) => ~ f m cs) MCP MCP' ->
        ContextSegment f (notfinished (m,cs,p) MCP) (notfinished (m,cs,p) MCP')
    | CSNot : forall MCP MCPpre MCPsuff MCP' m cs p,
        head MCP = (m,cs,p) ->
        ~ f m cs ->
        SplitInclusive (fun '(m,cs,p) => f m cs) MCP MCPpre MCPsuff ->
        ContextSegment f MCPsuff MCP' ->
        ContextSegment f MCP MCP'
    | CSSkip : forall MCP MCPpre MCPsuff MCP' m cs p,
        head MCP = (m,cs,p) ->
        f m cs ->
        SplitInclusive (fun '(m,cs,p) => f m cs) MCP MCPpre MCPsuff ->
        ContextSegment f MCPsuff MCP' ->
        ContextSegment f MCP MCP'
    .
  End WITH_STATE.

  Arguments WithContext {_}  _ _ _ _.
  Arguments ContextSegment {_} _ _ _.
  Arguments ObsOfMCP {_}.
  Arguments MCPState {_}.
  Arguments MCPTrace {_}.
  Arguments cstate {_}.
  
  (* Now let's rephrase our ad-hoc code safety property into one that is slightly
     less ad hoc, that now protects components any time they're marked as code, even
     if they changed later in the execution. Note that we instantiate the context state
     with our domain map, and its initial state and update function. 

     Here we use context segment to always give us a pair of adjacent states in the form
     of (notfinished (m,cs,p) (finished (m',cs',p'))). *)
  Definition CodeSafetyWithContext : Prop :=
    forall minit MCP m cs p m' cs' p' k,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = code ->
      m k = m' k.

  (* We have enough to start working on a more complex property: coroutine safety.
     Coroutine safety is intuitively the property that when a coroutine is active -
     determined by the stack pointer pointing somewhere in its stack - no other
     stack should be read or written. Let's start with something close to our
     code safety - coroutine integrity, just the property that we can't write
     to a stack while it's inactive.

     This looks very much like code safety, except that only care about protecting
     k when the k is in a stack that is not active. We call this a hyper-eager
     property, because just as with code safety, we always look at pairs of states. *)
  Definition CoroutineIntegrityHyperEager : Prop :=
    forall minit MCP m cs p m' cs' p' k sid fd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = stack sid fd ->
      activeStack sm m <> sid ->
      m k = m' k.

  (* We haven't yet seen any confidentiality properties - properties guaranteeing the
     secrecy of components, in this case components in an inactive stack. Let's stick
     to the hyper-eager style for now. We'll introduce a few new concepts.

     Firstly: confidentiality is expressed in terms of "variant" states. A k-variant
     state of m is a state that agrees with m at every component other than k. It may also
     agree at k. The intuition is that if the step from a state does the same thing as the
     step from its k-variant, we can't tell from that step what k was, so k is secret.
     We characterize "does the same thing" as producing the same output and changing
     state in the same way. *)
  Definition variantOf (k : Component) (m n : MachineState) :=
    forall k', k <> k' -> m k' = n k'.

  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (m k <> m' k \/ n k <> n' k) ->
      m' k = n' k.

  Definition CoroutineConfidentialityHyperEager : Prop :=
    forall minit MCP m cs p o m' cs' p' k sid fd n n' o',
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP  (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = stack sid fd ->
      activeStack sm m <> sid ->
      variantOf k m n ->
      step n = (n',o) ->
      mpstep (m,p) = Some (m',p',o') ->
      (o = o' /\ sameDifference m m' n n').

  (* Now there are strange things that happen with a hyper-eager property.
     Consider a program where a coroutine writes to a location in another stack, then
     reads the same location; this would be a violation of hyper-eager confidentiality,
     but in principle nothing secret has been revealed (only erased, violating integrity.)

     We therefore want a confidentiality property for coroutines that treats as secret
     the specific values in hidden locations at the time that control passes to a coroutine that
     shouldn't read them. This means varying the first state of a subtrace from when we leave a
     coroutine to when we return to it, and checking that for the entire subtrace, behavior
     is unchanged as above. Behavior is more complicated now, as the original trace might have
     three different qualities:

     1. it might end with a final state where the coroutine that can read k is active
     2. it might end prematurely, due to a fail stop
     3. it might diverge and run forever without reaching the appropriate coroutine

     In case 1, the variant trace should reach a *convergent* state, one that is also in that coroutine.
        The traces should be observationally equivalent and the convergent states should be same-different.
     In case 2, the variant trace will not end, but its observations should be prefixed by the original.
     In case 3, the variant trace should be observationally equivalent to the original.

     We need to introduce some predicates on states to talk about these traces having similar
     behavior. Stuck represents a trace that fail-stops before ever returning to the coroutine
     whose data is being protected. *)

  Definition Stuck (MPO : MPOTrace) : Prop :=
    exists m p o,
      Last MPO (m,p,o) ->
      mpstep (m,p) = None.

  (* We will use this definition of trace confidentiality in many contexts! *)
  Definition TraceConfidentiality (MCP:MCPTrace)  (k:Component) (Converge:MachineState -> Prop) : Prop :=
    forall m (cs:DomainMap) p n MO NO,
      head MCP = (m,cs,p) ->
      ObsOfMCP MCP MO -> (* We will mostly operate on the observation-annotated trace MO *)
      variantOf k m n ->
      PrefixUpTo (fun '(n',o) => Converge n') (RunOf n) NO ->
         (* Case 1 *)
      (forall mend p o,
          Last MO (mend,p,o) ->
          ~ Stuck MO ->
          exists nconv o',
            Last NO (nconv, o') /\
            ObsOfMP MO ~=_O ObsOfM NO /\
            sameDifference m mend n nconv)
      /\ (* Case 2 *)
      (Infinite MO ->
       ObsOfMP MO ~=_O ObsOfM NO)
      /\ (* Case 3 *)
      (Stuck MO ->
       ObsOfMP MO <=_O ObsOfM NO).

  (* Coroutine confidentiality: for each component k belonging to stack sid,
     for each trace segment where sid is inactive, trace confidentiality holds
     with convergence meaning that sid becomes active. *)
  Definition CoroutineConfidentialityEager : Prop :=
    forall minit MCP MCP' k sid fd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      initD k = stack sid fd ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      TraceConfidentiality MCP' k (fun n => activeStack sm n = sid).

  (* Let's give a similar treatment to integrity. Suppose we wanted to test integrity
     of a system with coroutines. We don't actually need to check at every step that integrity
     is maintained; if we're considering a component that belongs to a coroutine, we need only
     check that from when that coroutine is inactive to when it becomes active again, the
     component remains unchanged. So we can examine a trace for integrity of a component: *)
  Definition TraceIntegrity (MCP:MCPTrace) (k:Component) : Prop :=
    forall m (cs:DomainMap) p m' cs' p',
      head MCP = (m,cs,p) ->
      Last MCP (m',cs',p') ->
      m k = m' k.
  (* Note that if MCP is infinite, it fulfills trace integrity trivially. *)

  (* Now we have our eager, but not hyper-eager, coroutine integrity.
     It is similar to the confidentiality property. *)
  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP MCP' k sid fd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      initD k = stack sid fd ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      TraceIntegrity MCP' k.

  (* Notice how coroutines have the nice property that a stack is always
     either active or inactive, and we can always read and write the active
     stack and never an inactive one. Confidentiality and integrity won't
     always line up, even in more interesting coroutine models, and certainly
     not in our subroutine model. We introduce a concept of contours to
     keep track of these separate security concepts.

     A contour is just a map from a component to a pair of levels:
     - LC/HC: low and high confidentiality
     - LI/HI: low and high integrity
     (See machine.v for the definition of contour)

     So far we've seen code being (LC,HI) and stacks being (LC,LI) vs. (HC,HI).
     What kinds of components are (HC,LI)? Most notably ones that are uninitialized.
     We'll get into that more, but first lets use contours with the ideas we've just
     seen to create a very general property. *)

  Definition SafetyProperty (C : MachineState -> DomainMap -> Contour)
             (SegmentProp : Component -> MachineState -> DomainMap -> Prop) :=
    forall minit MCP MCP' k m c p,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (SegmentProp k) MCP MCP' ->
      head MCP' = (m,c,p) ->
      (integrityOf ((C m c) k) = HI ->
       TraceIntegrity MCP k) /\
      (confidentialityOf ((C m c) k) = HC ->
       TraceConfidentiality MCP k (fun m => ~ SegmentProp k m c)).

  (* See how we can reimplement our code and coroutine properties as instances of this safety property. *)
  Definition CodeContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | code => (LC,HI)
      | _ => (LC,LI)
      end.
  
  Definition CodeSafety : Prop :=
    SafetyProperty CodeContour (fun _ _ _ => False).

  Definition CoroutineContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | stack sid fd =>
        if sidEq (Some sid) (Some (activeStack sm m))
        then (LC,LI)
        else (HC,HI)
      | _ => (LC, LI)
      end.

  Definition CoroutineSafety : Prop :=
    forall sid,
      SafetyProperty CoroutineContour (fun _ m _ => activeStack sm m <> sid).

  (* Now lets implement stack safety in this style. The subroutine property is a
     little more complicated than previous ones. We will need to peel back nested
     stack domains to find whether a component has been shared. *)
  Fixpoint nestedStatus (fd:FrameD) : ObjD :=
    match fd with
    | active o _ => o
    | sealed fd => nestedStatus fd
    end.

  (* If a component is secret in the active frame, it is to be treated
     as uninitialized: (HC,LI).
     If it is secret and sealed, it is instead (HC,HI).
     But if it is sealed but shared, the sharing overrides the sealing
     and it is (LC,LI).
     At some point it may be useful to distinguish a read-only sharing that is (LC,HI).*)
  Definition SubroutineContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | stack sid (active secret _) => (HC,LI)
      | stack sid fd =>
        match nestedStatus fd with
        | local => (HC,HI)
        | shared => (LC,LI)
        end
      | _ => (LC,LI)
      end.

  Inductive FrameContains : FrameD -> FrameD -> Prop :=
  | FCEq : forall fd1 fd2,
      fd1 = fd2 ->
      FrameContains fd1 fd2
  | FCActive : forall fd1 fd2 od,
      FrameContains fd1 fd2 ->
      FrameContains (active od (Some fd1)) fd2
  | FCSealed : forall fd1 fd2,
      FrameContains fd1 fd2 ->
      FrameContains (sealed fd1) fd2.

  Definition TopFCContains (td:TopD) (fd:FrameD) : Prop :=
    exists sid fd',
      td = stack sid fd' /\ FrameContains fd' fd.
      
  Definition StackSafety : Prop :=
    forall fd,
      SafetyProperty SubroutineContour (fun k m dm => TopFCContains (dm k) fd).

End WITH_MAPS.
  
(* This file covers a version of the trace properties in which an arbitrary state
   is carried alongside the machine state from which we will extrace a context.*)
Section WITH_CONTEXT_STATE.

  (* Moving on, we now discuss our trace properties, integrity and confidentiality.
     These are properties of an MCPtrace and a component, intended to be applied to the subtraces
     from ContourSegment - they treat the final state, if any, as a special end state
     where they check what has changed over the course of the trace.

     First, we need to check the contour of the subtrace, which is derived from
     the contour state of its head, to see how the component should behave. So we
     have a parameter of the map from contour states to contours. *)
    
(***** Integrity *****)

(* First, we have ContourTraceIntegrity, which holds on a trace MCP and component k if
   the first and last machine states agree on k. A segment that is infinite never breaks
   integrity. *)

  (* Two machine states are variants at k if they agree on every component except k *)

  (* We can define a lazy version of trace integrity that does not check that k is
     the same, but allows it to differ as long as it is never (APT: observably?) accessed.
     The execution from the final state is compared to that of a run from any
     k-variant, and the property holds if the protected execution is an
     observational prefix of the variant. *)
  Definition ContourTraceIntegrityLazy (MCP:MCPTrace) (k:Component) : Prop :=
    forall m cs p m' cs' p',
      head MCP = (m,cs,p) ->
      Last MCP (m',cs',p') ->
      m k <> m' k ->  
      forall m'', variantOf k m' m'' ->
                  ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf  m'').

  (* We might instead reset k to what it was initially. *)
  Definition RollbackInt (k:Component) (Mstart Mend : MachineState) : MachineState :=
    fun k0 => if keqb k k0 then Mstart k0 else Mend k0.

  (* This produces an even weaker property, in which it is permissible to
     alter k and even to later access it, as long as the remaining execution 
     is not observably changed. Such scenarios are easy to construct relative 
     to a well-understood program, such as multiplying a value that is always
     treated as a boolean by a nonzero constant, but are difficult to generalize. *)
Definition ContourTraceIntegrityLazier (MCP:MCPTrace) (k:Component) : Prop :=
  forall m cs p m' cs' p',
    head MCP = (m,cs,p) ->
    Last MCP (m',cs',p') ->
    ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf (RollbackInt k m m')).

Lemma LazierWeaker : forall MCP k, ContourTraceIntegrityLazy MCP k -> ContourTraceIntegrityLazier MCP k.
Proof.
   unfold ContourTraceIntegrityLazy, ContourTraceIntegrityLazier.
   intros.
   unfold RollbackInt.
   destruct (WordEqDec (m k) (m' k)). 
   - apply MPRunPrefRun. simpl. 
     apply functional_extensionality. intros. destruct (keqb k x) eqn:?. 
     apply keqb_implies_eq in Heqb.  subst. auto.  auto. 
   - eapply H; eauto.
     unfold variantOf.
     intros. 
     destruct (keqb k k') eqn:?.
     apply keqb_implies_eq in Heqb. rewrite Heqb in H2. contradiction H2; auto.  auto.
Qed.

(***** Confidentiality *****)

(* Intuitively, consider the #s to denote when a component is high confidentiality
   as execution moves across several security domains:
     |   d1  |  d2   |   d3   |
  k1 [###############]
  k2         [################]
  
  We need to make sure that k1 is not read (does not impact execution) from the
  start of domain d1 to the end of d2. Same for k2 across d2 and d3. So what matters
  is only the start and end of a contiguous block of high confidentiality. *)

(* Two pairs of states m, m', n, and n' are "delta matched" if all components that changed
   from m to m' or from n to n' are equal in m' and n'.
 
   In context, m and n will be variants, and m' and n' will be states that are reached
   in their execution. m' and n' may not be identical because the original variation
   may be present, but if they have changed differently, that would mean that the variation
   had an effect on the state. *)

(* We define a proposition for a trace that terminates, not because it is cut off due to
   reaching the f2 criterion, but because its policy fail-stops. *)

(* Broadly, the trace confidentiality property will take a k-variant of the original
   trace and run it until its state converges with the final state of the original.
   Then it will need to behave appropriately in three cases:

   - If the original trace ended successfully (meaning that its final state is LC at k),
     then the variant should reach a state that converges, and it should delta-match
     with regard to the initial variant states. In addition, the interim observational
     traces should match.

   - If the original trace is infinite, its observational trace should match that of
     the variant, which is always infinite (because it has no policy to stop it short.)

   - If the original trace gets stuck, then its observational trace should prefix that
     of the variant, which has no policy to get it stuck.
*)
Definition ContourTraceConfidentiality (MCP:MCPTrace)  (k:Component) : Prop :=
  forall m cs p m' MO MOv,
    head MCP = (m,cs,p) ->
    ObsOfMCP MCP MO -> (* We will mostly operate on the observation-annotated trace MCP' *)
    variantOf k m m' -> (* We consider all states m' that are k-variants from m *)
    PrefixUpTo (fun '(m',o) => Converge m m') (RunOf m') MOv ->
    (* And run m' to get an observation-annotated trace *)
    (* These traces are related in their behavior. They either both converge, both diverge, or the
       original trace gets stuck (fail-stops).*)
    (forall mend p o,
        Last MO (mend,p,o) ->
        ~ Stuck MO ->
        exists m'converge o',
          Last MOv (m'converge, o') /\ (* then the variant's trace will reach a state that converges *)
          ObsOfMP MO ~=_O ObsOfM MOv /\
          (* both traces have the same observations *)
          deltaMatch m mend m' m'converge) /\ (* the converging states have changed identically *)
    (Infinite MO -> (* if the original trace is infinite, so is the variant, and their traces match *)
     ObsOfMP MO ~=_O ObsOfM MOv) /\
    (Stuck MO -> (* and if the original fail-stops, its trace is a prefix of that of the variant *)
     ObsOfMP MO <=_O ObsOfM MOv).
(* APT: Didn't study carefully. *)
End WITH_CONTOUR_STATE.


  (* Now that we've described confidentiality and integrity in terms of contours,
     we just need to instantiate the properties by defining how routines and coroutines
     manipulate the contour state and how it translates into a contour. *)

  (* All of our properties will use the same contour state: a domain map.
     The initial domain map uses some of our other program maps to establish
     which addresses belong to each stack. All stacks are active, and their
     sharing status is secret, because they have not been initialized.
     Any memory that isn't code or a stack is heap, and we mostly ignore it. *) 
  Definition ContourState := DomainMap.


  
  (* Here's a very simple property: code is always low confidentiality and high integrity.
     So the contour maps code to (LC,HI), and everything else to (LC,LI) *)



  (* For coroutines, the active stack is accessible.
     All other stacks are inaccessible, and everything else is accessible.

     Note that this formulation is fine with changing the stack pointer
     outside of a yield and then accessing a different stack. It takes
     yield integrity to enforce that stacks only change on yields. *)




  (* APT: need an argument about why considering just a single component at a time captures right intuition. *)

  (* In each of these properties, we've quantified over all components k and then checked
     integrity and confidentiality of k specifically. We could imagine a version of, for instance,
     confidentiality, where we vary multiple components simultaneously and see if that variation
     changes behavior. Varying a single component is no stronger, because a variation where one
     component is identical subsumes it. It is actually weaker: consider taking x || y, where
     x and y are high confidentiality and initialized to 1. *)

