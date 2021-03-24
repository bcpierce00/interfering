From StackSafety Require Import Trace.

(* Primitive Abstraction. *)

Module Type MachineSpec. 

  Parameter Word : Type. 
  Parameter wlt : Word -> Word -> bool.
  Parameter weq : Word -> Word -> bool.
  Axiom WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.
  Axiom weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.
  Axiom not_weq_implies_neq :
    forall w1 w2,
      weq w1 w2 = false -> w1 <> w2.
  Definition wle (w1 w2: Word) : bool := orb (wlt w1 w2) (weq w1 w2).
  Parameter wplus : Word -> nat -> Word.
  Parameter wminus : Word -> nat -> Word.
  
  Parameter wplus_neq : forall w n, n > 0 -> w <> wplus w n.

  Definition Addr : Type := Word.

Parameter Register : Type.
Parameter SP : Register.
Parameter regEq : Register -> Register -> bool.

Inductive Component:=
| Mem (a:Addr)
| Reg (r:Register)
| PC.

Parameter keqb : Component -> Component -> bool.
Axiom keqb_implies_eq :
  forall k1 k2,
    keqb k1 k2 = true -> k1 = k2.
Axiom not_keqb_implies_neq :
  forall k1 k2,
    keqb k1 k2 = false -> k1 <> k2.

(* A Value is a Word. *)
Definition Value : Type := Word.

(* A Machine State is just a map from Components to Values. *)
Parameter MachineState : Type.
Definition View := Component -> Value.
Parameter proj : MachineState -> View.


(* Observations are values, or silent (tau) *)
Inductive Observation : Type := 
| Out (w:Value) 
| Tau. 

(* A Machine State can step to a new Machine State plus an Observation. *)
Parameter step : MachineState -> MachineState * Observation.

Parameter FunID : Type.
Parameter StackID : Type.

Definition EntryMap := Addr -> bool.

Definition StackMap := Addr -> option StackID.

Inductive CodeAnnotation :=
| call
| ret
| yield
| share (f: MachineState -> Addr -> option bool)
| normal
.

Inductive CodeStatus :=
| inFun : FunID -> CodeAnnotation -> CodeStatus
| notCode : CodeStatus
.

Definition CodeMap := Addr -> CodeStatus.

(* Stack ID of stack pointer *)
Definition activeStack (sm: StackMap) (m: MachineState) :
  option StackID :=
  sm (proj m (Reg SP)).

Parameter stack_eqb : StackID -> StackID -> bool.

Definition optstack_eqb (o1 o2 : option StackID) : bool :=
  match o1, o2 with
  | Some n1, Some n2 => stack_eqb n1 n2
  | None, None => true
  | _, _ => false
  end.

Definition AnnotationOf (cdm : CodeMap) (a:Addr) : option CodeAnnotation :=
  match cdm a with
  | inFun f normal => None
  | inFun f ann => Some ann
  | notCode => None
  end.

Definition isCode' (cdm : CodeMap) (a:Addr) : bool :=
  match cdm a with
  | inFun _ _ => true
  | notCode => false
  end.

(*Definition isCall (cm: CallMap) (m: MachineState) (lay: Layout) : Prop :=
  cm (m (Reg PC)) = Some lay.*)

Definition justRet (mc m: MachineState) : Prop :=
  proj m PC = wplus (proj mc PC) 4 /\ proj m (Reg SP) = proj mc (Reg SP).

Definition justRet_dec mc m : {justRet mc m} + {~ justRet mc m}.
Proof.
  unfold justRet.
  destruct (WordEqDec (proj m PC) (wplus (proj mc PC) 4));
    destruct (WordEqDec (proj m (Reg SP)) (proj mc (Reg SP)));
    try solve [left; auto];
    right; intros [? ?]; auto.
Qed.

Parameter PolicyState : Type.

(* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
Definition MPState : Type := MachineState * PolicyState.
Definition ms (mp : MPState) := fst mp.
Definition ps (mp : MPState) := snd mp.

Parameter WFInitMPState : MPState -> Prop.

Parameter mpstep : MPState -> option (MPState * Observation).
Axiom mpstepCompat :
  forall m p o m' p',
    mpstep (m,p) = Some (m',p',o) ->
    step m = (m',o).

(********* Steps and Traces ***********)

Definition MTrace := TraceOf MachineState.

CoFixpoint MTraceOf (M : MachineState) : MTrace :=
  notfinished M (MTraceOf (fst (step M))).

Definition MPTrace := TraceOf MPState.

CoFixpoint MPTraceOf (mp : MPState) : MPTrace :=
  match mpstep mp with
  | None => finished mp
  | Some (mp',o) => notfinished mp (MPTraceOf mp')
  end.

Definition MTrace' := TraceOf (MachineState * Observation).

CoFixpoint RunOf (m : MachineState) : MTrace' :=
  notfinished (m,snd (step m)) (RunOf (fst (step m))).

Definition MPTrace' := TraceOf (MachineState * PolicyState * Observation).

CoFixpoint MPRunOf (mp : MPState) : MPTrace' :=
  match mpstep mp with
  | None =>
    finished (mp,Tau)
  | Some (mp',o) =>
    notfinished (mp,o) (MPRunOf mp')
  end.

(********** Machine Lemmas ************)
Lemma MTraceOfInf :
  forall m,
    infinite (MTraceOf m).
Proof.  
  intros m m' H.
  remember (MTraceOf m) as M.
  generalize dependent m.
  induction H; intros m HeqM.
  - rewrite (idTrace_eq (MTraceOf m)) in HeqM.
    simpl in *.
    inversion HeqM.
  - rewrite (idTrace_eq (MTraceOf m)) in HeqM.
    simpl in *.
    inversion HeqM; subst; clear HeqM.
    eapply IHLast; eauto.
Qed.

Lemma MPTraceOfHead: forall mp, mp = head (MPTraceOf mp).
Proof.
  intros. destruct mp.  simpl. 
  destruct (mpstep (m,p)); auto; destruct p0; auto.
Qed.

(* ******************* Trace stuff ********************* *)

(* We need to associate domainmaps with a trace. Here is some helpful machinery for associating
   states in general with a trace. *)
Section WITH_STATE.
  Variable CtxState : Type.
  Variable CtxStateUpdate : MachineState -> CtxState -> CtxState.
  Variable initCtx : CtxState.
  
  Definition MPCState : Type := MachineState * PolicyState * CtxState.
  Definition MPCTrace := TraceOf MPCState.
  Definition mstate : MPCState -> MachineState := fun '(m,p,cs) => m.
  Definition pstate : MPCState -> PolicyState := fun '(m,p,cs) => p.
  Definition cstate : MPCState -> CtxState := fun '(m,p,cs) => cs.

  Definition mpcstep (mpc:MPCState) : option (MPCState * Observation) :=
    option_map
      (fun '(m,p,o) => (m,p,CtxStateUpdate m (cstate mpc),o))
      (mpstep (mstate mpc,pstate mpc)).
  
  Inductive StepsTo : MPCState -> MPCState -> Prop :=
  | already : forall mpc, StepsTo mpc mpc
  | future : forall mpc mpc' mpc'' o,
      StepsTo mpc mpc' ->
      mpcstep mpc' = Some (mpc'',o) ->
      StepsTo mpc mpc''.

  Inductive StepsToWhenObs (P:MPCState -> Prop) : MPCState -> MPCState -> TraceOf Observation -> Prop :=
  | when : forall mpc,
      P mpc ->
      StepsToWhenObs P mpc mpc (finished Tau)
  | futureWhen : forall mpc mpc' mpc'' o O,
      ~ P mpc ->
      mpcstep mpc = Some (mpc',o) ->
      StepsToWhenObs P mpc' mpc'' O ->
      StepsToWhenObs P mpc mpc'' (notfinished o O).

  Definition StepsToWhen P mpc mpc' := exists O, StepsToWhenObs P mpc mpc' O.

  Inductive FullObsTrace : MPCState -> TraceOf Observation -> Prop :=
  | stepIt : forall mpc mpc' o O,
      mpcstep mpc = Some (mpc',o) ->
      FullObsTrace mpc' O ->
      FullObsTrace mpc (notfinished o O).

  Definition NeverStepsToObs P mpc O :=
    FullObsTrace mpc O /\
    forall mpc',
      ~ StepsToWhen P mpc mpc'.

  Definition Reachable (mpc:MPCState) : Prop :=
    exists mpinit,
      WFInitMPState mpinit /\ StepsTo (mpinit,initCtx) mpc.

  CoFixpoint MPCTraceOf (mpc : MPCState) : MPCTrace :=
    match mpcstep mpc with
    | None => finished mpc
    | Some (mpc',o) => notfinished mpc (MPCTraceOf mpc')
    end.

  CoInductive MPCTraceToWhen (P:MPCState -> Prop) : MPCState -> MPCTrace -> Prop :=
  | TTWNow : forall mpc,
      P mpc ->
      MPCTraceToWhen P mpc (finished mpc)
  | TTWNever : forall mpc,
      mpcstep mpc = None ->
      MPCTraceToWhen P mpc (finished mpc)
  | TTWLater : forall mpc mpc' o MPC,
      ~ P mpc ->
      mpcstep mpc = Some (mpc',o) ->
      MPCTraceToWhen P mpc' MPC ->
      MPCTraceToWhen P mpc (notfinished mpc MPC)
  .
  
  (* Similarly, with WithObs we relate an MCPTrace into the MPOTrace
     corresponding to its steps annotated with their observations. We feed
     each step's observation forward, to line up with the machine state that follows that step.
     We will need this later. *)
  Inductive WithObs (o:Observation) : MPCTrace -> TraceOf Observation -> Prop :=
  | WOFinished : forall mpc,
      WithObs o (finished mpc) (finished o)
  | WONotfinished : forall mpc mpc' o' MPC O,
      WithObs o' MPC O ->
      mpcstep mpc = Some (mpc',o') ->
      WithObs o (notfinished mpc MPC) (notfinished o O).
  
  (* ObsOfMCP starts the observation with Tau, reflecting that initially
     there is no observation until a step occurs. *)
  Definition ObsOfMPC := WithObs Tau.
  
  (* Segment relates two MCPTraces given a condition f on mpc states,
     where the second is a longest subtrace of the first such that f holds on all elements
     except the final. So, it will always have at least two elements, and its head will have been
     preceded by one on which f does not hold, while the last (if any) also does not have f hold.
     
     We will use this machinery to clip out sections of a trace that we want to check
     against a property, with the final state reflecting the state after some relevant execution.
   *)
  Inductive Segment (f : MPCState -> Prop) : MPCTrace -> MPCTrace -> Prop :=
  | SegCurrent : forall MPC MPC' mpc,
      f mpc ->
      PrefixUpTo (fun mpc' => ~ f mpc') MPC MPC' ->
      Segment f (notfinished mpc MPC) (notfinished mpc MPC')
  | SegNot : forall MPC MPCpre MPCsuff MPC' mpc,
      ~ f mpc ->
      SplitInclusive f MPC MPCpre MPCsuff ->
      Segment f MPCsuff MPC' ->
      Segment f (notfinished mpc MPC) MPC'
  | SegSkip : forall MPC MPCpre MPCsuff MPC' mpc,
      f mpc ->
      SplitInclusive f MPC MPCpre MPCsuff ->
      Segment f MPCsuff MPC' ->
      Segment f (notfinished mpc MPC) MPC'
  .

  Definition ReachableSegment (f : MPCState -> Prop) (MPC:MPCTrace) : Prop :=
    exists mpinit,
      WFInitMPState mpinit /\ Segment f (MPCTraceOf (mpinit,initCtx)) MPC.

  Lemma ReachableStepsToWhenSegment :
    forall mpc mpc' P,
      Reachable mpc ->
      StepsToWhen P mpc mpc' ->
      exists MPC,
        ReachableSegment P MPC /\
        head MPC = mpc /\
        Last MPC mpc'.
  Proof.
  Admitted.
(*    intros. destruct H0 as [O]. induction H0.
    - exists (finished mpc).
      split.
      + unfold ReachableSegment.
        unfold Reachable in H.
        destruct H as [mpinit]; exists mpinit.
        destruct H. split; auto. *)
        

End WITH_STATE.

Arguments Segment {_} _ _ _.
Arguments ObsOfMPC {_}.
Arguments MPCState {_}.
Arguments MPCTrace {_}.
Arguments cstate {_}.
Arguments mstate {_}.
Arguments pstate {_}.
Arguments Reachable {_} _ _ _.
Arguments mpcstep {_} _ _.
Arguments MPCTraceOf {_} _.
Arguments MPCTraceToWhen {_} _ _ _.
Arguments StepsToWhenObs {_} _ _ _ _.
Arguments StepsToWhen {_} _ _ _.
Arguments ReachableSegment {_} _ _ _.
Arguments NeverStepsToObs {_} _ _ _.

End MachineSpec.
