Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* This file covers a version of the trace properties in which the contour
   is updated at each step. The contour can also remember the history of the
   execution, carrying some arbitrary extra 
   
   First we define the annotation of a trace with contours given some contour
   update function. *)
Section WITH_CONTOUR_UPDATE.

  Variable ContourState : Type.

  Definition MCPState : Type := MachineState * Contour * PolicyState.
  Definition MCPTrace := TraceOf MCPState.
  Definition MPOTrace := MPTrace'.

  Variable ContourStateUpdate : MachineState -> ContourState -> ContourState.
  Variable OfState : ContourState -> Contour.

  (* WithContour relates an MPTrace to its MCPTrace given an initial contour state cs.
     A finished trace (m,p) is related to (m,OfState c,p).
     We relate a trace (notfinished (m,p) MP) to (notfinished (m,OfState c,p) MCP),
     where MP relates to MCP given cs' produced by ContourStateUpdate. Additionally,
     the relation requires that MP begin with m' and p' produced by mpstep (m,p),
     so that only MPTraces produced by the step function relate to any MCPTrace *)
  Inductive WithContour (cs:ContourState) : MPTrace -> MCPTrace -> Prop :=
  | WCFinished : forall m p,
      WithContour cs (finished (m,p)) (finished (m,OfState cs,p))
  | WCNotfinished : forall m p cs' m' p' o MP MCP,
      mpstep (m,p) = Some (m',p',o) ->
      ContourStateUpdate m cs = cs' ->
      WithContour cs' MP MCP ->
      head MP = (m',p') -> (* This checks that MP is actually real *)
      WithContour cs (notfinished (m,p) MP) (notfinished (m,OfState cs,p) MCP).
  
  (* Similarly, we with WithObs turn an MCPTrace into the appropriate MPOTrace
     with the observations of its steps. We always feed the observation produced
     by a step forward, to line up with the machine state that follows that step. *)
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

End WITH_CONTOUR_UPDATE.

(* ContourSegment relates two MCPTraces such that the first contains the second,
   and the second is a longest subtrace subject to an initial and final condition, as follows.
   
   For MCP to relate to MCP' given conditions f1 and f2, f1 must hold on the head of MCP',
   and f2 must not hold on any element of its tail except the final element if there is one.
   (So f1 and f2 may both hold on the head of MCP', but if f2 holds on the next element MCP'
   must be of length two.) Otherwise we take elements forever, or until we reach one on which
   f2 holds.

   f1 can be thought of as the condition that tells our property it needs to pay attention
   to a subtrace, and f2 the condition that indicates that it needs to check whether something
   has changed.
 *)
Inductive ContourSegment (f1 f2 : Contour -> Prop) : MCPTrace -> MCPTrace -> Prop :=
| CSCurrent : forall MCP MCP' m c p,
    f1 c ->
    PrefixUpTo (fun '(m,c,p) => f2 c) MCP MCP' ->
    ContourSegment f1 f2 (notfinished (m,c,p) MCP) (notfinished (m,c,p) MCP')
| CSNot : forall MCP MCPpre MCPsuff MCP' m c p,
    head MCP = (m,c,p) ->
    ~ f1 c ->
    SplitInclusive (fun '(m,c,p) => f1 c) MCP MCPpre MCPsuff ->
    ContourSegment f1 f2 MCPsuff MCP' ->
    ContourSegment f1 f2 MCP MCP'
| CSSkip : forall MCP MCPpre MCPsuff MCP' m c p,
    head MCP = (m,c,p) ->
    f1 c ->
    SplitInclusive (fun '(m,c,p) => f2 c) MCP MCPpre MCPsuff ->
    ContourSegment f1 f2 MCPsuff MCP' ->
    ContourSegment f1 f2 MCP MCP'
.

(***** Integrity *****)

(* For integrity of a component k, we let f1 be the property that k is High Integrity *)
Definition highInt (k:Component) := fun c => integrityOf (c k) = HI.
(* And we let f2 be the property that k is either Low Integrity or Low Confidentiality *)
Definition lowCI (k:Component) := fun c => confidentialityOf (c k) = LC \/ integrityOf (c k) = LI.

(* The intuition is: if we see that a component is high integrity, we want to make sure that it
   doesn't change until it is once again low integrity. We can check constantly, but if it is
   high confidentiality, nothing should be reading it anyway; so it suffices to check that it is
   unchanged only when it is low integrity or high [APT:low??] confidentiality, whichever comes first. *)
(* APT: confidentiality part seems debateable.   Should integrity really depend on what is potentially readable rather than being based on observability? And if so, why should we check when integrity goes to LI if confidentiality never goes to LC? *)

(* APT: need an argument about why considering just a single component at a time captures right intuition. *)

(* Putting everything together, we have ContourTraceIntegrity, which holds on a trace if
   for each component and every segment defined as above with regard to k, the first and
   last machine states agree on k. A segment that is infinite never breaks integrity, because
   k is never meant to be read again. *)
Definition ContourTraceIntegrity (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' c' p',
    ContourSegment (highInt k) (lowCI k) MCP MCP' ->
    head MCP' = (m,c,p) ->
    Last MCP' (m',c',p') ->
    m k = m' k.

(* Two machine states are variants at k if they agree on every component except k *)
(* APT: Fixed *)
Definition variantOf (k : Component) (m n : MachineState) :=
  forall k', k <> k' -> m k' = n k'.

(* We can define a lazy version of trace integrity that does not check that k is
   the same, but allows it to differ as long as it is never (APT: observably?) accessed.
   The execution from the final state is compared to that of a run from any
   k-variant, and the property holds if the protected execution is an
   observational prefix of the variant. *)
Definition ContourTraceIntegrityLazy (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' c' p',
    ContourSegment (highInt k) (lowCI k) MCP MCP' ->
    head MCP' = (m,c,p) ->
    Last MCP' (m',c',p') ->
    m k <> m' k ->  
    forall m'', variantOf k m' m'' ->
                ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf  m'').

(* We might instead reset k to what it was initially. *)
(* APT: fixed *)
Definition RollbackInt (k:Component) (Mstart Mend : MachineState) : MachineState :=
  fun k0 => if keqb k k0 then Mstart k0 else Mend k0.

(* This produces an even weaker property, in which it is permissible to
   alter k (APT: even if it _is_ later accessed), as long as the remaining execution is not (APT observably) changed, perhaps
   by coincidence. (APT: This needs clarification. *)
Definition ContourTraceIntegrityLazier (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' c' p',
    ContourSegment (highInt k) (lowCI k) MCP MCP' ->
    head MCP' = (m,c,p) ->
    Last MCP' (m',c',p') ->
    ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf (RollbackInt k m m')).

Lemma LazierWeaker : forall MCP, ContourTraceIntegrityLazy MCP -> ContourTraceIntegrityLazier MCP.
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
     apply keqb_implies_eq in Heqb. rewrite Heqb in H3. contradiction H3; auto.  auto.
Qed.


(***** Confidentiality *****)

(* Our f1 and f2 conditions are now just that confidentiality is high, then low. *)
Definition highConf (k:Component) := fun c => confidentialityOf (c k) = HC.
Definition lowConf (k:Component) := fun c => confidentialityOf (c k) = LC.

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
Definition deltaMatch (m m' n n' : MachineState) :=
  forall k,
    (m k <> m' k \/ n k <> n' k) ->
    m' k = n' k.

(* We define a proposition for a trace that terminates, not because it is cut off due to
   reaching the f2 criterion, but because its policy fail-stops. *)
Definition Stuck (MPO : MPOTrace) : Prop :=
  exists m p o,
    Last MPO (m,p,o) ->
    mpstep (m,p) = None.

(* For now, we define convergence of two states as sharing return to a common program counter
   and stack pointer. Eventually we may want it to be more general. *)
Definition Converge (m1 m2 : MachineState) :=
  m1 (Reg SP) = m2 (Reg SP) /\ m1 (Reg PC) = m2 (Reg PC).

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
Definition ContourTraceConfidentiality (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' MO MOv,
    ContourSegment (highConf k) (lowConf k) MCP MCP' -> (* We consider all subtraces MCP' where any k is HC *)
    head MCP' = (m,c,p) ->
    ObsOfMCP MCP' MO -> (* We will mostly operate on the observation-annotated trace MCP' *)
    variantOf k m m' -> (* We consider all states m' that are k-variants from m *)
    RunOf m' = MOv -> (* And run m' to get an observation-annotated trace *)
    (* These traces are related in their behavior. They either both converge, both diverge, or the
       original trace gets stuck (fail-stops).*)
    (forall mend c p,
        Last MCP' (mend,c,p) ->
        confidentialityOf (c k) = LC -> (* if we actually get to low confidentiality *)
        exists m'converge o',
          InTrace (m'converge, o') MOv /\ (* then the variant's trace will reach a state that converges *)
          Converge mend m'converge /\
          ObsOfMP MO ~=_O ObsOfM MOv /\ (* TODO: this needs to be the prefix *)
          (* both traces have the same observations *)
          deltaMatch m mend m' m'converge) /\ (* the converging states have changed identically *)
    (Infinite MO -> (* if the original trace is infinite, so is the variant, and their traces match *)
     ObsOfMP MO ~=_O ObsOfM MOv) /\
    (Stuck MO -> (* and if the original fail-stops, its trace is a prefix of that of the variant *)
     ObsOfMP MO <=_O ObsOfM MOv).
(* APT: Didn't study carefully. *)


(* In this section we will describe Domains, which describe the layout of code in our model.
   We will map components to domains as the ContourState, and that mapping may change during execution.
   Domains have a tree structure, because a component can belong to multiple domains. *)
Section DomainTree.

  (* In our stack safety property, we will be marking some addresses as shared and some as secret.
     "shared" can also be thought of as a special form of initialization; it indicates that an address'
     value on a domain transition should be treated as intentional. "Secret" means that even if it might
     be accessible, its current value at a transition should be considered uninitialized.

     To link this concept directly to stack safety, when a subroutine is called with arguments, the
     arguments are shared, and the stack above the stack pointer is secret, as it could have any value. *)
  Inductive ShareStatus :=
  | shared
  | secret
  .

  (* Our first actual domain is a Stack Domain. It has two forms: the active frame (everything above the
     stack pointer on entry) and a sealed stack (everything below). Of course a component that is in a
     sealed stack is also in some frame, and in fact may be in multiple nested sealed stacks.

     In our actual properties, a component that is just in the active frame is always writeable;
     sharing determines how components are treated once they are at least one level down. *)
  Inductive StackD :=
  | active : ShareStatus -> StackD
  | sealed : StackD -> StackD
  .

  (* Finally, the top-level domain type can make a component part of a stack (in which case
     it also needs to know which stack id it belongs to). It can also be code, in the heap, or
     a register. Later we can expand the definition of the heap to extend the model. *)
  Inductive Domain :=
  | stack : StackID -> StackD -> Domain
  | code
  | heap
  | registers
  .

  Definition DomainMap := Component -> Domain.
  
End DomainTree.

Section WITH_MAPS.

  (* Now that we've described confidentiality and integrity in terms of contours,
     we just need to instantiate the properties by defining how routines and coroutines
     manipulate the contour state and how it translates into a contour. *)

  Variable cdm : CodeMap'.
  Variable sm : StackMap.
  Variable mpInit : MPState.

  (* All of our properties will use the same contour state: a domain map.
     The initial domain map uses some of our other program maps to establish
     which addresses belong to each stack. All stacks are active, and their
     sharing status is secret, because they have not been initialized.
     Any memory that isn't code or a stack is heap, and we mostly ignore it. *) 
  Definition ContourState := DomainMap.
  Definition initCS : ContourState :=
    fun k =>
      match k with
      | Mem a =>
        if isCode' cdm a
        then code
        else match findStack sm a with
             | Some sid => stack sid (active secret)
             | None => heap
             end
      | _ => registers
      end.

  (* Our update function checks the annotation on the code being executed.
     Annotations are defined in Machine.v as an alternative to a million different
     maps, and the ones that matter are call, return, yield, and share.

     The share annotation takes a component that will be shared, which is only meaningful
     if the component is part of a stack.
     APT: I'm not quite clear where these annotations get attached.

     Note that yields don't actually change the contour state, as they don't change which
     addresses belong to which stacks. *)
  Definition updateCS (m:MachineState) (cs:ContourState) :=
    match AnnotationOf cdm (m (Reg PC)) with
    | Some call =>
      fun k =>
        match k, cs k with
        | Mem a, stack sid sd =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) && wlt a (m (Reg SP))
          then stack sid (sealed sd)
          else cs k
        | _,_ => cs k
        end
    | Some ret =>
      fun k =>
        match cs k with
        | stack sid (sealed sd) =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then
            stack sid sd
          else cs k
        | _ => cs k
        end
    | Some (share k0) =>
      fun k =>
        if keqb k k0 then
          match cs k with
          | stack sid (active secret) => stack sid (active shared)
          | _ => cs k
          end
        else cs k
    | _ => cs
    end.


  (* Here's a very simple property: code is always low confidentiality and high integrity.
     So the contour maps code to (LC,HI), and everything else to (LC,LI) *)
  Definition CodeContour (cs:ContourState) : Contour :=
    fun k =>
      match cs k with
      | code => (LC,HI)
      | _ => (LC,LI)
      end.

  (* So our definition of CodeSafety is general safety instantiated with CodeInit and CodeUpdate *)
  (* APT:???*)
  Definition CodeSafety :=
    forall MCP,
      WithContour ContourState updateCS CodeContour initCS (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\
      ContourTraceConfidentiality MCP.    

  (* For coroutines, the active stack is accessible.
     All other stacks are inaccessible, and everything else is accessible.

     Note that this formulation is fine with changing the stack pointer
     outside of a yield and then accessing a different stack. It takes
     yield integrity to enforce that stacks only change on yields. *)
  Definition CoroutineContour (cs:ContourState) : Contour :=
    fun k =>
      match cs k with
      | stack sid sd =>
        if sidEq (Some sid) (findStack sm (ms mpInit (Reg SP)))
        then (LC,LI)
        else (HC,HI)
      | _ => (LC, LI)
      end.

  Definition CoroutineSafety :=
    forall MCP,
      WithContour ContourState updateCS CoroutineContour initCS (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\
      ContourTraceConfidentiality MCP.
  

  (* The subroutine property is a little more complicated. We will
     need to peel back nested stack domains to find whether a component has
     been shared. *)
  Fixpoint nestedStatus (sd:StackD) : ShareStatus :=
    match sd with
    | active s => s
    | sealed sd => nestedStatus sd
    end.

  (* If a component is secret in the active frame, it is to be treated
     as uninitialized: (HC,LI).
     If it is secret and sealed, it is instead (HC,HI).
     But if it is sealed but shared, the sharing overrides the sealing
     and it is (LC,LI).
     At some point it may be useful to distinguish a read-only sharing that is (LC,HI).*)
  Definition SubroutineContour (cs:ContourState) : Contour :=
    fun k =>
      match cs k with
      | stack sid (active secret) => (HC,LI)
      | stack sid sd =>
        match nestedStatus sd with
        | secret => (HC,HI)
        | shared => (LC,LI)
        end
      | _ => (LC,LI)
      end.
  
  Definition StackSafety :=
    forall MCP,
      WithContour ContourState updateCS SubroutineContour initCS (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\
      ContourTraceConfidentiality MCP.

End WITH_MAPS.
