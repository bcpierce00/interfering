Require Import Coq.Lists.List.
Import List.ListNotations.

From StackSafety Require Import Trace.

Module Type Machine.

(*  Axiom exception : forall {A}, string -> A.
  Extract Constant exception =>
  "(fun l ->
         let s = Bytes.create (List.length l) in
          let rec copy i = function
          | [] -> s
          | c :: l -> Bytes.set s i c; copy (i+1) l
          in failwith (""Exception: "" ^ Bytes.to_string (copy 0 l)))". *)


  Parameter Word : Type.

  Parameter wlt : Word -> Word -> bool.

  Parameter weq : Word -> Word -> bool.

  Parameter WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.

  Parameter weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.

  Parameter not_weq_implies_neq :
    forall w1 w2,
      weq w1 w2 = false -> w1 <> w2.

  Parameter wle : Word -> Word -> bool.
  
  Parameter wplus : Word -> nat -> Word.

  Parameter wminus : Word -> nat -> Word.

  Parameter wplus_neq : forall w (n : nat),
      (n > O)%nat -> w <> wplus w n.

  Definition Addr := Word.

  Parameter Register : Type.

  Parameter RA : Register.
  Parameter SP : Register.
  Parameter regEq : Register -> Register -> bool.
  
  Inductive Component:=
  | Mem (a:Addr)
  | Reg (r:Register)
  | PC.

  Parameter keqb : Component -> Component -> bool.

  Parameter Value : Type.
  Parameter vtow : Value -> Word.

  Parameter MachineState : Type.
  Definition View := Component -> Value.

  Parameter proj : MachineState -> Component -> Value.
  Parameter projw : MachineState -> Component -> Word.

  Parameter proj_vtow : forall m k, vtow (proj m k) = projw m k.

  (* Maybe name this pullback instead *)
  Parameter jorp : MachineState -> Component -> Value -> MachineState.
  
  Parameter getComponents : MachineState -> list Component.
  
  (* Observations are ObsType, or silent (tau) *)
  Parameter ObsType : Type.
  
  Inductive Observation : Type := 
  | Out (o:ObsType) 
  | Tau. 

  (* A Machine State can step to a new Machine State plus an Observation. *)
  Parameter step : MachineState -> MachineState * Observation.

  Parameter FunID : Type.
  Parameter StackID : Type.

  (*Definition EntryMap := Addr -> bool.*)

  Definition StackMap := Addr -> option StackID.

  Inductive CodeAnnotation : Type :=
  | call
  | retrn
  | yield
  | scall (f: MachineState -> Addr -> bool)
  | normal
  .

(*  Inductive CodeStatus :=
  | inFun   : FunID -> CodeAnnotation -> CodeStatus
  | notCode : CodeStatus
  .*)
  
  Definition CodeMap := Addr -> option CodeAnnotation.

  Parameter activeStack : StackMap -> MachineState -> option StackID.
   
  Parameter stack_eqb : StackID -> StackID -> bool.

  Parameter optstack_eqb : option StackID -> option StackID -> bool.

  Parameter justRet : MachineState -> MachineState -> Prop.

  Parameter justRet_dec : forall mc m, {justRet mc m} + {~ justRet mc m}.
End Machine.

Module Type Policy(M:Machine).
  Import M.

  Parameter PolicyState : Type.

  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.

  Parameter pstep : MPState -> option PolicyState.

  Parameter mpstep : MPState -> option (MPState * Observation).

  Parameter mpstepCompat :
    forall m p o m' p',
      mpstep (m,p) = Some (m',p',o) ->
      step m = (m',o).

  Parameter WFInitMPState : MPState -> Prop.

End Policy.

Module Type Ctx (M:Machine).
  Import M.

  Parameter CtxState : Type.
  Parameter CtxStateUpdate : MachineState -> CtxState -> CtxState.
  Parameter initCtx : MachineState -> CtxState.
End Ctx.

Module Type MapMaker (M : Machine).
  Import M.

  Parameter cdm : CodeMap.
  Parameter sm : StackMap.
  Parameter defaultStack : StackID.
End MapMaker.

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

(*Arguments Segment {_} _ _ _.
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
Arguments FullObsTrace {_} _ _. *)

