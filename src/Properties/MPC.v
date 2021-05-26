From StackSafety Require Import Trace MachineModule PolicyModule CtxModule.

Module MPC (M:Machine) (P:Policy M) (C:Ctx M).
  Import M.
  Import P.
  Import C.
         
  Definition MPCState : Type := MachineState * PolicyState * CtxState.
  Definition MPCTrace := TraceOf MPCState.
  Definition mstate : MPCState -> MachineState := fun '(m,p,cs) => m.
  Definition pstate : MPCState -> PolicyState := fun '(m,p,cs) => p.
  Definition cstate : MPCState -> CtxState := fun '(m,p,cs) => cs.
  
  (********** Machine Lemmas ************)
  (* TODO: redo for MPCTraces *)
  (*Lemma MTraceOfInf :
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
    (* destruct (mpstep (m,p)); auto; destruct p0; auto. *)
    (* Qed. *)
  Abort. (* FIXME *) *)

  Definition mpcstep (mpc:MPCState) : option (MPCState * Observation) :=
    option_map
      (fun '(m,p,o) => (m,p,CtxStateUpdate (mstate mpc) (cstate mpc),o))
      (mpstep (mstate mpc,pstate mpc)).
  
  Inductive StepsTo : MPCState -> MPCState -> Prop :=
  | already : forall mpc, StepsTo mpc mpc
  | future : forall mpc mpc' mpc'' o,
      StepsTo mpc mpc' ->
      mpcstep mpc' = Some (mpc'',o) ->
      StepsTo mpc mpc''.

  Inductive StepsToWhenObs (P:MPCState -> Prop)
    : MPCState -> MPCState -> TraceOf Observation -> Prop :=
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
      WFInitMPState mpinit /\ StepsTo (mpinit,initCtx (fst mpinit)) mpc.

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
      WFInitMPState mpinit /\ Segment f (MPCTraceOf (mpinit,initCtx (fst mpinit))) MPC.

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
        
End MPC.
