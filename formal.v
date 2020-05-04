Require Import List.
Import ListNotations.
Require Import Bool.

Section foo.

(* TODO: Make all this match the terminology in the .tex -- e.g., a
   Contour should correspond to a MachineState, not to a Trace,
   etc. *)

(* Primitive Abstractions. *)
  
Variable Word : Type.
Variable wlt : Word -> Word -> bool.
Variable weq : Word -> Word -> bool.
Definition wle (w1 w2: Word) : bool := orb (wlt w1 w2) (weq w1 w2).
Variable wplus : Word -> nat -> Word. 
Variable wminus : Word -> nat -> Word. 

Variable WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.

Definition Addr : Type := Word.

Variable Register : Type.
Variable PC : Register.
Variable SP : Register.
Variable O : Register. (* "output register" *)

Inductive Component:=
| Mem (a:Addr)
| Reg (r:Register).

(* A Value is a Word. *)
Definition Value : Type := Word.

(* A Machine State is just a map from Components to Values. *)
Definition MachineState := Component -> Value.

(* Observations are values, or silent (tau) *)
Inductive Observation :=
| Out (w : Word)
| Tau.

(* A Machine State can step to a new Machine State plus an Observation. *)
Variable step : MachineState -> option (MachineState * Observation).
(* APT: Why is there an option here? Machines run forever... *)

(*******************)
(***** Traces ******)
(*******************)

CoInductive Trace (A : Type) : Type :=
| finished : A -> Trace A
| notfinished : A -> Trace A -> Trace A.

Arguments finished {_} _.
Arguments notfinished {_} _ _.

Definition idTrace {A} (MM: Trace A) : Trace A := 
  match MM with 
  | finished M => finished M 
  | notfinished M MM' => notfinished M  MM'
  end.

Lemma idTrace_eq : forall {A} (MM: Trace A), MM = idTrace MM. 
   destruct MM; reflexivity.
Qed.

Definition head {A} (MM : Trace A) : A :=
  match MM with
  | finished M => M
  | notfinished M _ => M
  end.

Inductive InTrace {A} (m:A) : Trace A -> Prop :=
| In_finished : InTrace m (finished m)
| In_now : forall MM, InTrace m (notfinished m MM)                        
| In_later : forall m' MM, InTrace m MM -> InTrace m (notfinished m' MM).

Lemma head_InTrace :forall {A} (MM: Trace A), InTrace (head MM) MM.
Proof.
  intros.
  destruct MM. 
  - constructor.
  - simpl. constructor.
Qed.

CoFixpoint mapTrace {A B:Type} (f:A -> B) (MM: Trace A) : Trace B :=
  match MM with
  | finished M => finished (f M)
  | notfinished M MM' => notfinished (f M) (mapTrace f MM')
  end.

CoInductive ForallTrace {A:Type} (P:A -> Prop) : Trace A -> Prop :=
| Forall_finished : forall M, P M -> ForallTrace P (finished M)
| Forall_notfinished : forall M MM', P M -> ForallTrace P MM' -> ForallTrace P (notfinished M MM')
.

CoInductive TraceEq {A} : Trace A -> Trace A -> Prop :=
| EqFin : forall m, TraceEq (finished m) (finished m)
| EqCons : forall m mm1 mm2, TraceEq mm1 mm2 ->
                             TraceEq (notfinished m mm1) (notfinished m mm2).

CoFixpoint TraceApp {A} (MM: Trace A) (MMO: option (Trace A)) : Trace A :=
  match MM with
  | finished m =>
    match MMO with
    | Some m' => notfinished m m'
    | None => MM
    end
  | notfinished m MM' => notfinished m (TraceApp MM' MMO)
  end.

Notation "MM1 ^ MM2" := (TraceApp MM1 MM2).

Definition OptTraceApp {A} (MMO1: option (Trace A)) (MMO2: option (Trace A)) : option (Trace A) :=
  match MMO1 with
  | Some MM => Some (TraceApp MM MMO2)
  | None => MMO2
  end.

Notation "MM1 ?^ MM2" := (OptTraceApp MM1 MM2) (at level 80).

Lemma TraceAppHead {A} :
  forall (MM NN : Trace A) (NNO : option (Trace A)),
    MM = NN ^ NNO -> head MM = head NN.
Proof.
  intros MM NN NNO App.
  destruct NN as [a | a NN].
  - rewrite App.
    simpl.
    destruct NNO; simpl; auto.
  - rewrite App.
    simpl.
    auto.
Qed.

    (* LEO: TODO: Should we define TracePrefix based on TraceSpan? *)
(* TracePrefix MM1 MM2 says MM2 is a prefix of MM1. *)
CoInductive TracePrefix {A} : Trace A -> Trace A -> Prop :=
| PrefixEq  : forall m, TracePrefix (finished m) (finished m)
| PrefixNow : forall m mm, TracePrefix (notfinished m mm) (finished m)
| PrefixLater : forall m mm1 mm2, TracePrefix mm1 mm2 ->
                                  TracePrefix (notfinished m mm1)
                                              (notfinished m mm2).

(* Divide MM1 into MM2 ++ MMO such that MM2 is the longest prefix for which P holds on each element *)
Definition TraceSpan {A} (P : A -> Prop) (MM1 MM2 : Trace A) (MMO : option (Trace A)) : Prop :=
  MM1 = MM2^MMO /\ ForallTrace P MM2 /\
  forall MM2', TracePrefix MM1 MM2'->
    ForallTrace P MM2' ->
    TracePrefix MM2 MM2' .

(* MM2 is the longest prefix of MM1 for which P holds on each element. *)
Definition LongestPrefix {A} (P : A -> Prop) (MM1 MM2 : Trace A) : Prop :=
  exists MMO, TraceSpan P MM1 MM2 MMO.

Inductive IsEnd {A} : Trace A -> A -> Prop :=
| IsEndNow : forall M, IsEnd (finished M) M
| IsEndLater : forall MM M M', IsEnd MM M -> IsEnd (notfinished M' MM) M
.

(* Definition tail {A} (MM: Trace A) : option (Trace A) := *)
(*   match MM with *)
(*   | finished _ => None *)
(*   | notfinished _ M => Some M *)
(*   end. *)
  
(* Fixpoint ith {A} (i:nat) (MM: Trace A) : option A := *)
(*   match i with *)
(*   | O => Some (head MM) *)
(*   | S i' => match tail MM with *)
(*             | Some MM' => ith i' MM' *)
(*             | None => None                               *)
(*             end *)
(*   end. *)

(* Lemma head_ith : forall {A} (MM: Trace A), ith O MM = Some (head MM). *)
(* Proof. *)
(*   destruct MM. *)
(*   - auto. *)
(*   - auto. *)
(* Qed. *)

Definition MTrace := Trace MachineState.

CoFixpoint traceOf (M : MachineState) : MTrace :=
  match step M with
  | None => finished M
  | Some (M',_) => notfinished M (traceOf M')
  end.

(* Confidentiality and Integrity Labels *)
Inductive CLabel :=
| HC
| LC.

Inductive ILabel :=
| HI
| LI.

Definition Label := (CLabel * ILabel)%type.

Definition Contour := Component -> Label.

Definition integrityOf (l : Label) : ILabel := snd l.
Definition confidentialityOf (l : Label) : CLabel := fst l.

(****************************)
(***** Eager Integrity ******)
(****************************)

(* Latex-like definition. *)
Definition EagerStackIntegrity (C : Contour) (MM: MTrace) : Prop :=
    forall (k: Component), integrityOf (C k) = HI ->
      forall (m: MachineState), InTrace m MM -> (head MM) k = m k.

(* CoInductive variant *)
CoInductive EagerStackIntegrity' (C : Contour) : MTrace -> Prop :=
| SI_finished : forall M, EagerStackIntegrity' C (finished M)
| SI_notfinished :
    forall (M0: MachineState) (MM: MTrace),
    (forall (k: Component), integrityOf (C k) = HI ->
                            M0 k = (head MM) k) ->
    EagerStackIntegrity' C MM ->
    EagerStackIntegrity' C (notfinished M0 MM).


Lemma StackIntegrityEquiv : forall (C:Contour) (MM: MTrace),
     EagerStackIntegrity C MM -> EagerStackIntegrity' C MM.
Proof.
  cofix COFIX.
  intros.
  destruct MM. 
  - constructor.
  - constructor.
    + intros. unfold EagerStackIntegrity in H.  simpl in H. 
      apply H; auto. constructor. apply head_InTrace. 
    + apply COFIX. 
      unfold EagerStackIntegrity in *.  intros. simpl in H. 
      erewrite <- H; auto. 
      * apply H; auto.  constructor. auto.
      * constructor. apply head_InTrace.
Qed.

Lemma StackIntegrity'Equiv : forall (C:Contour) (MM: MTrace),
     EagerStackIntegrity' C MM -> EagerStackIntegrity C MM.
Proof.
  intros.
  unfold EagerStackIntegrity. 
  intros.
  induction H1. 
  - auto.
  - auto.
  - simpl. inversion H. subst. rewrite <- IHInTrace.
    +  apply H4; auto. 
    +  inversion H.  auto.
Qed.

Definition variantOf (M N : MachineState) (C : Contour) :=
  forall (k : Component), confidentialityOf (C k) = LC ->
                          M k = N k.

(* LEO: I'm not sure how to satisfy productivity here. We're essentially trying
   to filter a trace. *)
Definition ObsTrace := Trace Observation.

CoFixpoint ObsTraceOf (MM: MTrace) : ObsTrace :=
  match MM with
  | finished m =>
    finished Tau
  | notfinished M MM' =>
    match step M with
    | Some (M', O) =>
      notfinished O (ObsTraceOf MM')
    | None => (* Shouldn't happen in wf MTrace *)
      notfinished Tau (ObsTraceOf MM') 
    end
  end.

(*
Definition ObsTraceOf (MM : MTrace) : ObsTrace :=
  mapTrace (fun M => option_map snd (step M)) MM.

Definition Obs (M : MachineState) := M (Reg O).



(* Stuttering version *)
Definition ObsTraceOf' (MM : MTrace) := mapTrace Obs MM.

(* SNA: alternative obs: non-stuttering trace of output register *)
CoFixpoint ObsTraceOf (MM : MTrace) : Trace Value :=
  match MM with
  | finished M =>
    finished (M (Reg O))
  | notfinished M Ms =>
    let v := M (Reg O) in 
    match Ms with
    | finished M' =>
      let v' := M' (Reg O) in 
      if weq v v'
      then finished v
      else notfinished v (finished v')
    | notfinished M' Ms' =>
      let v' := M' (Reg O) in
      if weq v v'
      then notfinished v (ObsTraceOf Ms')
      else notfinished v (ObsTraceOf (notfinished M' Ms'))
    end
  end.
 *)
(* Alternate: steps have observations (options or tau) and obstrace concatenates
   non-taus. *)
(* LEO: Can't do this. It's not productive. Unless I'm missing something. *)
(*
Definition EagerStackConfidentiality (C : Contour) (MM : MTrace) := 
  forall N, variantOf (head MM) N C ->
            let o  := ObsTraceOf MM in
            let o' := ObsTraceOf (traceOf N) in
            TracePrefix o' o. (* \/ TracePrefix o o') *)
*)
(* APT: just this direction: it would be bad if variant trace ended sooner than reference, right? *)
(* LEO: I'm not sure about only one observation being a prefix of the other. What if the variant machine tries halts because of the monitor? Are we termination-sensitive? *)
(* APT: Ah, right.  I guess we have to be termination-insensitive. *)
(* APT+SEAN: On third thought, we're not sure we buy this. Why should the variant be allowed 
to fail-stop more often than the reference trace? *)

CoInductive ObsTraceEq : Trace Observation -> Trace Observation -> Prop :=
| ObsEqTau1 : forall OO OO',
    ObsTraceEq OO OO' ->
    ObsTraceEq (notfinished Tau OO) OO'
| ObsEqTau2 : forall OO OO',
    ObsTraceEq OO OO' ->
    ObsTraceEq OO (notfinished Tau OO')
| ObsEqNow : forall w OO OO',
    ObsTraceEq OO OO' ->
    ObsTraceEq (notfinished (Out w) OO) (notfinished (Out w) OO')
| ObsEqFinishedOut : forall w,
    ObsTraceEq (finished (Out w)) (finished (Out w))
| ObsEqFinishedTau : 
    ObsTraceEq (finished Tau) (finished Tau)
(* The last thing we need is a way of handling *all-tau* traces.
   There are a couple of ways of doing that, not sure what will
   play better in proofs. *)
| ObsEqAllTau : forall OO,
     ObsTraceEq OO OO.
(* APT: Establishing equality between traces seems hard, and this overlaps 
the previous two cases.  Maybe try:
   ForallTrace (fun o => o = Tau) OO -> 
   ForallTrace (fun o => o = Tau) OO' -> 
   ObsTraceEq OO OO'
? 
LEO: That was the other thing I had in mind. I'll see what makes proofs easier.
(Note that this proposal overlaps with the first two cases, as well as the last one.)
*)


(* SNA: Proposed confidentiality property for eager policy; actual and variant traces
   have identical observation traces and a final state in the actual trace has a
   corresponding pre-return state in the variant, where all changes are indistinguishable. *)
Definition EagerStackConfidentiality (C : Contour) (MM : MTrace) (isRet : MachineState -> Prop) :=
  forall N NN Mret, variantOf (head MM) N C ->
               LongestPrefix (fun M => ~ isRet M) NN (traceOf N) -> 
               ObsTraceEq (ObsTraceOf MM) (ObsTraceOf NN) /\
               (IsEnd MM Mret -> 
                exists Nret, IsEnd NN Nret /\
                forall k, (head MM) k <> Mret k \/ (head NN) k <> Nret k 
                  -> Nret k = Mret k). 
(* BCP queried: should we also require that MM terminates if NN terminates? *)

CoInductive StrongEagerStackConfidentiality (R : MachineState -> Prop) :
  MTrace -> MTrace -> Prop :=
| StrongConfStep :
    forall M MM N NN O,
      step M = Some (head MM, O) ->
      step N = Some (head NN, O) ->
      (forall k, head MM k <> M k \/ head NN k <> N k -> head MM k = head NN k) ->
      StrongEagerStackConfidentiality R MM NN ->
      StrongEagerStackConfidentiality R (notfinished M MM) (notfinished N NN)
| StrongConfEnd :
    forall M N,
      R M -> R N ->
      StrongEagerStackConfidentiality R (finished M) (finished N).

Definition frob {A} (MM : Trace A) : Trace A :=
  match MM with
  | finished a => finished a
  | notfinished a MM' => notfinished a MM'
  end.

Lemma frob_eq : forall {A} (MM : Trace A), MM = frob MM.
Proof.
  destruct MM; auto.
Qed.

Lemma confStepPreservesVariant :
  forall C M M' OM N N' ON,
    step M = Some (M', OM) -> step N = Some (N', ON) ->
    (forall k, M' k <> M k \/ N' k <> N k -> M' k = N' k) ->
    variantOf M N C ->
    variantOf M' N' C.
Proof.
  unfold variantOf.
  intros C M M' OM N N' ON StepM StepN Conf Var k Hk.
  destruct (WordEqDec (M' k) (M k)) as [eqM | neqM];
  destruct (WordEqDec (N' k) (N k)) as [eqN | neqN];
  try solve [ apply Conf; auto ];
  rewrite eqM; rewrite eqN; auto.
Qed.

Lemma StrongConfImpliesObsEq :
  forall C R MM NN,
    variantOf (head MM) (head NN) C ->
    StrongEagerStackConfidentiality R MM NN ->
    ObsTraceEq (ObsTraceOf MM) (ObsTraceOf NN).
Proof.
  cofix COFIX.
  intros C R MM NN Var Conf.
  inversion Conf; simpl.
  - match goal with
    | [ |- ObsTraceEq ?T1 ?T2 ] =>
      rewrite (frob_eq T1); rewrite (frob_eq T2); simpl
    end.
    repeat match goal with
           | [ H : step ?M = _ |- context[step ?M] ] => rewrite H; simpl
           end.
    destruct O0.
    + apply ObsEqNow.
      eapply COFIX; eauto.
      eapply confStepPreservesVariant; eauto.
      assert (head MM = M) as HM
          by (destruct H3; auto).
      assert (head NN = N) as HN
          by (destruct H4; auto).
      rewrite <- HM.
      rewrite <- HN.      
      apply Var.
    + apply ObsEqTau1.
      apply ObsEqTau2.
      eapply COFIX; eauto.
      eapply confStepPreservesVariant; eauto.
      assert (head MM = M) as HM
          by (destruct H3; auto).
      assert (head NN = N) as HN
          by (destruct H4; auto).
      rewrite <- HM.
      rewrite <- HN.      
      apply Var.
  - match goal with
    | [ |- ObsTraceEq ?T1 ?T2 ] =>
      rewrite (frob_eq T1); rewrite (frob_eq T2); simpl
    end.
    apply ObsEqFinishedTau.
Qed.

Lemma ComponentConfTrans :
  forall (M0 M1 M2 N0 N1 N2 : MachineState),
    (forall k : Component, M1 k <> M0 k \/ N1 k <> N0 k -> M1 k = N1 k) ->
    (forall k : Component, M1 k <> M2 k \/ N1 k <> N2 k -> N2 k = M2 k) ->
    (forall k : Component, M0 k <> M2 k \/ N0 k <> N2 k -> N2 k = M2 k).
Proof.
  intros M0 M1 M2 N0 N1 N2 H01 H12.
  intros k [HM02 | HN02].
  - destruct (WordEqDec (M2 k) (M1 k)) as [eqM | neqM].
    + assert (M1 k <> M0 k) as HM01.
      { intros Contra.
        apply HM02.
        rewrite Contra in eqM.
        auto.
      }
      specialize (H01 k (or_introl HM01)).
      destruct (WordEqDec (N2 k) (N1 k)) as [eqN | neqN].
      * rewrite eqM; rewrite eqN; auto.
      * apply H12; eauto.
    + eapply H12; eauto.
  - destruct (WordEqDec (N2 k) (N1 k)) as [eqN | neqN].
    + assert (N1 k <> N0 k) as HN01.
      { intros Contra.
        apply HN02.
        rewrite Contra in eqN.
        auto.
      }
      specialize (H01 k (or_intror HN01)).
      destruct (WordEqDec (M2 k) (M1 k)) as [eqM | neqM].
      * rewrite eqM; rewrite eqN; auto.
      * apply H12; eauto.
    + eapply H12; eauto.
Qed.

Lemma StrongConfImpliesEndConf :
  forall C R MM NN,
    variantOf (head MM) (head NN) C ->
    StrongEagerStackConfidentiality R MM NN ->
    forall Mret,
      IsEnd MM Mret ->
      exists Nret : MachineState,
        IsEnd NN Nret /\
        forall k, (head MM) k <> Mret k \/ (head NN) k <> Nret k  ->
                  Nret k = Mret k. 
Proof.
  intros C R MM NN Var Conf Mret HEnd.
  generalize dependent NN.
  induction HEnd; subst; eauto; intros NN Var Conf.
  - inversion Conf; subst; eauto; clear Conf.
    exists N.
    split; [ constructor |].
    simpl; intros k Hk.
    inversion Hk; exfalso; eauto.
  - inversion Conf; subst; eauto; clear Conf; simpl in *.
    destruct (IHHEnd NN0) as [Nret [InNRet HNRet]]; eauto.
    + eapply confStepPreservesVariant; eauto.
    + exists Nret.
      split.
      * constructor; auto.
      * eapply ComponentConfTrans; eauto.
Qed.        

Theorem StrongConfImpliesConf (C: Contour) (R: MachineState -> Prop) (MM : MTrace) :
  (forall (NN : MTrace),
    variantOf (head MM) (head NN) C ->
    StrongEagerStackConfidentiality R MM NN) ->
  EagerStackConfidentiality C MM R.
Proof.
  intros Conf.
  intros N NN MRet HVar [MMO [App [NotR Pref]]].
  specialize (Conf NN).
  assert (head NN = N) as HN.
  { apply TraceAppHead in App.
    rewrite App.
    simpl.
    destruct (step N); simpl; auto.
    destruct p; simpl; auto.
  }
  split.
  - eapply StrongConfImpliesObsEq; eauto.
    + rewrite HN; eauto.
    + eapply Conf.
      rewrite HN; eauto.
  - intros HEnd.
    eapply StrongConfImpliesEndConf; eauto.
    + rewrite HN; eauto.
    + eapply Conf.
      rewrite HN; eauto.
Qed.

Definition CallMap := Value -> nat -> Prop. 

Definition isCall (cm: CallMap) (M: MachineState) (args: nat) : Prop :=
   cm (M (Reg PC)) args.

Definition isRet (Mc M: MachineState) : Prop :=
  M (Reg PC) = wplus (Mc (Reg PC)) 4 /\ M (Reg SP) = Mc (Reg SP).

Definition updateContour (C: Contour) (args: nat) (M: MachineState) : Contour :=
  fun k =>
    match k with
    | Mem a => 
      let a' := wminus (M (Reg SP)) args in
      if wle a a' then
        (HC, HI)
      else if andb (wlt a' a) (wle a (M (Reg SP))) then
        (LC, LI)                  
      else if wlt (M (Reg SP)) a then
        (HC, LI)
      else C k (* impossible *)
    | _ => C k
    end.

(*
CoInductive Subtrace (cm: CallMap) : Contour -> MTrace -> Contour -> MTrace -> Prop :=
  | SubNow : forall C C' MM MM' args,
      (* Current instruction is a call *)
      isCall cm (head MM) args ->
      (* Take the prefix until a return *)
      LongestPrefix (fun M => ~ (isRet (head MM) M)) MM MM' ->
      (* Construct the new contour *)
      updateContour C args (head MM) = C' -> 
      Subtrace cm C MM C' MM'
  | SubNotNow: forall C MM C' MM' M,
      (forall args, ~ isCall cm (head MM) args) -> 
      Subtrace cm C MM C' MM' ->
      Subtrace cm C (notfinished M MM) C' MM'
  | SubSkipCall : forall C MM C' MMskip args MM' MM'',
      isCall cm (head MM) args -> 
      TraceSpan (fun M => ~ (isRet (head MM) M)) MM MMskip (Some MM')  -> 
      Subtrace cm C MM' C' MM'' ->
      Subtrace cm C MM C' MM''.
*)
CoInductive Subtrace (cm: CallMap) : Contour -> MTrace -> Contour -> MTrace -> Prop :=
  | SubNow : forall C C' MM MM' args,
      (* Current instruction is a call *)
      isCall cm (head MM) args ->
      (* Take the prefix until a return *)
      LongestPrefix (fun M => ~ (isRet (head MM) M)) MM MM' ->
      (* Construct the new contour *)
      updateContour C args (head MM) = C' -> 
      Subtrace cm C MM C' MM'
  | SubNotNow: forall C MM C' MM' M,
      Subtrace cm C MM C' MM' ->
      Subtrace cm C (notfinished M MM) C' MM'.

(*
CoInductive StackSafety (cm : CallMap) : MTrace -> Contour -> Prop :=
  ss : forall (MM : MTrace) (C : Contour),
       (StackIntegrity C MM) ->
       (StackConfidentiality C MM) ->
       (forall MM' C', Subtrace cm C MM C' MM' -> StackSafety cm MM' C') ->
       StackSafety cm MM C.
*)
Definition EagerStackSafety (cm : CallMap) : MTrace -> Contour -> Prop :=
  fun (MM : MTrace) (C : Contour) =>
    (EagerStackIntegrity C MM) /\
    (EagerStackConfidentiality C MM (fun _ => False)) /\
    (forall MM' C', Subtrace cm C MM C' MM' ->
                    EagerStackIntegrity C' MM' /\
                    EagerStackConfidentiality C' MM' (isRet (head MM'))).

(* TODO: step by step property that implies the rest *)

(***** TESTING Property **********)
(* Note: This enforces lockstep due to PC equality.
   TODO: How not to enforce lockstep? *)

Definition EagerIntegrityTest (C : Contour) (M M' : MachineState) : Prop :=
  forall (k : Component), integrityOf (C k) = HI -> M k = M' k.

Definition EagerConfidentialityTest (isRet : MachineState -> Prop)  
           (M M' N N' : MachineState) (OM ON : Observation) : Prop :=
  OM = ON /\ 
  forall (k : Component),  M k <> M' k \/ N k <> N' k -> M' k = N' k.

(* Initial Machine State, Current Variant Machine State, Current Contour, isRet *)
Definition MNCR : Type :=
  MachineState * MachineState * Contour * (MachineState -> Prop).

Inductive MNCR_step : MNCR -> MNCR -> Prop :=
| ncr : forall M0 N N' C R,
    (exists O, step N = Some (N', O)) ->
    MNCR_step (M0,N,C,R) (M0, N',C,R).

Definition MNCRs_step (MNCRs MNCRs' : list MNCR) : Prop :=
  Forall2 MNCR_step MNCRs MNCRs'.

      (* Could also do this? *)
      (* EagerIntegrityTest C N N' -> *)

(* Invariant: MNCRs nonempty *)
CoInductive EagerStackSafetyTest (cm : CallMap) : MTrace -> list MNCR -> Prop :=
| EagerTestHalt :
    forall M MNCRs, 
    step M = None ->
    EagerStackSafetyTest cm (finished M) MNCRs
| EagerTestStep :
    forall M MM MNCRs MNCRs' M' OM,
      (* Not a call or a return *)
      (forall args, ~ isCall cm M args) ->
      (forall M0 N C R, In (M0,N,C,R) MNCRs -> ~ R M) ->
      (* Take a step. *)
      step M = Some (M', OM) ->      
      (* Enforce confidentiality for each variant. *)
      (forall M0 N C R,
          In (M0,N,C,R) MNCRs ->
          exists N' ON, step N = Some (N', ON) /\
          EagerConfidentialityTest R M M' N N' OM ON) ->
      (* Enforce integrity for main trace, but for each possible level in NCRs? *)
      (forall M0 N C R,
          In (M0,N,C,R) MNCRs ->
          EagerIntegrityTest C M M') ->
      (* Step all variants and just recurse *)
      MNCRs_step MNCRs MNCRs' ->
      head MM = M' ->
      EagerStackSafetyTest cm MM MNCRs' ->
      (* Conclude for current. *)
      EagerStackSafetyTest cm (notfinished M MM) MNCRs
| EagerTestCall :
    forall args M MM MNCRs MNCRs' M' OM C C',
      (* Is a call *)
      isCall cm M args ->
      (* (forall N C R, In (N,C,R) NCRs -> ~ R M) -> *)  
      (* Take a step. *)
      step M = Some (M', OM) ->      
      (* Enforce confidentiality for each variant. *)
      (forall M0 N C R,
          In (M0,N,C,R) MNCRs ->
          exists N' ON, step N = Some (N', ON) /\
          EagerConfidentialityTest R M M' N N' OM ON) ->
      (* Enforce integrity for main trace, but for each possible level in NCRs? *)
      (forall M0 N C R,
          In (M0,N,C,R) MNCRs ->
          EagerIntegrityTest C M M') ->
      (* Step all variants. *)
      MNCRs_step MNCRs MNCRs' ->
      head MM = M' ->
      (* Calculate the new contour based on the top of the variant stack. *)
      (exists M0 N0 C0 R0 MNCR0s, (M0,N0,C0,R0) :: MNCR0s = MNCRs /\
                                  updateContour C0 args M0 = C') ->
      (* Recurse with every variant at the new contour at the top. *)
      (forall Mvar, variantOf M Mvar C ->
                    EagerStackSafetyTest cm MM ((M, Mvar, C', isRet M) :: MNCRs')) ->
      (* Conclude for current. *)
      EagerStackSafetyTest cm (notfinished M MM) MNCRs
| EagerTestRet :
    forall M MM MNCRs MNCRs' M' OM,
      (* Is a return *)
      (* isCall cm M args -> *)
      (exists M0 N C R, In (M0,N,C,R) MNCRs /\ R M) ->
        (* (forall N C R, In (N,C,R) NCRs -> ~ R M) -> *)  
      (* Take a step. *)
      step M = Some (M', OM) ->      
      (* Enforce confidentiality for each variant. *)
      (forall M0 N C R,
          In (M0,N,C,R) MNCRs ->
          exists N' ON, step N = Some (N', ON) /\
          EagerConfidentialityTest R M M' N N' OM ON) ->
      (* Enforce integrity for main trace, but for each possible level in NCRs? *)
      (forall M0 N C R,
          In (M0,N,C,R) MNCRs ->
          EagerIntegrityTest C M M') ->
      (* Step all variants. *)
      MNCRs_step MNCRs MNCRs' ->
      (* Recurse but take of the top of the stack. *)
      head MM = M' ->
      EagerStackSafetyTest cm MM (tl MNCRs') ->
      (* Conclude for current. *)
      EagerStackSafetyTest cm (notfinished M MM) MNCRs.

Definition EagerStackSafetyTest' cm C MM :=
  forall N, variantOf (head MM) N C ->
  EagerStackSafetyTest cm MM [(head MM,N,C,fun _ => False)].

Ltac in_reasoning := 
  repeat match goal with
         | [ H : In _ [] |- _ ] => inversion H
         | [ H : In _ [_] |- _ ] => inversion H; subst; clear H
         | [ H : (_,_,_,_) = (_,_,_,_) |- _ ] => inversion H; subst; clear H
         end.

Lemma MNCR_step_preserves_in :
  forall M N C R MNCRs MNCRs' N' O,
  In (M,N,C,R) MNCRs ->
  Forall2 MNCR_step MNCRs MNCRs' ->
  step N = Some (N',O) ->
  In (M,N',C,R) MNCRs'.
Proof.
  intros.  
  induction H0.
  - inversion H.
  - inversion H; subst; eauto.
    + inversion H0; subst; eauto.
      destruct H8.
      rewrite H1 in H3.
      inversion H3; subst; left; auto.
    + right. apply IHForall2; auto.
Qed.

Inductive Last {A : Type} : A -> list A -> Prop :=
| LastSing : forall x, Last x [x]
| LastTail : forall x h t, Last x t -> Last x (h::t).

Lemma MNCR_step_preserves_last :
  forall M N C R MNCRs MNCRs' N' O,
  Last (M,N,C,R) MNCRs ->
  Forall2 MNCR_step MNCRs MNCRs' ->
  step N = Some (N',O) ->
  Last (M,N',C,R) MNCRs'.
Proof.
  intros.  
  induction H0.
  - inversion H.
  - inversion H; subst; eauto.
    + inversion H0; subst; eauto.
      destruct H8.
      rewrite H1 in H3.
      inversion H3; subst; auto.
      inversion H2; subst; auto.
      left; auto.
    + right. apply IHForall2; auto.
Qed.

Lemma Last_implies_In {A : Type} (x : A) (l : list A) :
  Last x l -> In x l.
Proof.  
  intros Last; induction Last.
  - left; auto.
  - right; auto.
Qed.

Theorem TestImpliesIntegrityToplevel :
  forall cm C MM MNCRs,
  (exists M N, Last (M,N,C,fun _ => False) MNCRs) ->
  EagerStackSafetyTest cm MM MNCRs -> EagerStackIntegrity' C MM.
Proof.
  cofix COFIX.
  intros cm C MM MCNRs HIn Safety.
  inversion Safety; subst.
  - apply SI_finished. 
  - apply SI_notfinished.
    + intros k Hk.
      unfold EagerIntegrityTest in *.
      destruct HIn as [M0 [N HIn]].
      eapply H3; [eapply Last_implies_In | ]; eauto.
    + apply (COFIX cm C MM0 MNCRs'); auto.
      destruct HIn as [M0 [N HIn]].
      unfold MNCRs_step in *.
      remember HIn as HLast; clear HeqHLast.
      apply Last_implies_In in HIn.
      destruct (H2 M0 N C (fun _ => False) HIn) as [N' [ON [HN' HConf]]].
      exists M0. exists N'.
      eapply MNCR_step_preserves_last; eauto.
  - apply SI_notfinished.
    + intros k Hk.
      unfold EagerIntegrityTest in *.
      destruct HIn as [M0 [N HIn]].
      eapply H2; [eapply Last_implies_In | ]; eauto.
    + apply (COFIX cm C MM0 ((M, M, C', isRet M) :: MNCRs')).
      * destruct HIn as [M0 [N HIn]].      
        unfold MNCRs_step in *.
        remember HIn as HLast; clear HeqHLast.
        apply Last_implies_In in HIn.
        destruct (H1 M0 N C (fun _ => False) HIn) as [N' [ON [HN' HConf]]].
        exists M0. exists N'. 
        right.
        eapply MNCR_step_preserves_last; eauto.
      * apply H6.
        unfold variantOf.
        auto.
  - apply SI_notfinished.
    + intros k Hk.
      unfold EagerIntegrityTest in *.
      destruct HIn as [M0 [N HIn]].
      eapply H2; [eapply Last_implies_In | ]; eauto.
    + apply (COFIX cm C MM0 (tl MNCRs')); auto.
      destruct HIn as [M0 [N HIn]].      
      unfold MNCRs_step in *.
      remember HIn as HLast; clear HeqHLast.
      apply Last_implies_In in HIn.
      destruct (H1 M0 N C (fun _ => False) HIn) as [N' [ON [HN' HConf]]].
      exists M0. exists N'.
      destruct MCNRs.
      * inversion H3; subst.
        inversion HLast.
      * destruct MNCRs'; inversion H3; subst.
        simpl.
        { inversion HLast; subst; clear HLast.
          - destruct H as [M1 [N1 [C1 [R1 [HIn1 HR]]]]].
            in_reasoning.
            inversion HR.
          - eapply MNCR_step_preserves_last; eauto.
        } 
Qed.

Theorem TestImpliesConfidentialityToplevel :
  forall cm C MM MNCRs,
  (exists M N, Last (M,N,C,fun _ => False) MNCRs) ->
  EagerStackSafetyTest cm MM MNCRs -> EagerStackConfidentiality C MM (fun _ => False).
Proof.
  intros cm C MM MNCRs HLast Safety.
  
  

  (* TODO2: this setup for lazy properties *)


(* ********* SNA Beware : Lazy Properties ********* *)

(* this variation of subtrace also gives us the suffix of the primary trace
   after the subtrace, or None if the subtrace is itself a suffix *)
CoInductive SubtraceWithSuffix (cm: CallMap) : Contour -> MTrace -> Contour -> MTrace -> option MTrace -> Prop :=
  | SubSufNow : forall C C' MM MM' MMO args,
      (* Current instruction is a call *)
      isCall cm (head MM) args ->
      (* Take the prefix until a return and maybe a suffix *)
      TraceSpan (fun M => ~ (isRet (head MM) M)) MM MM' MMO ->
      (* Construct the new contour *)
      updateContour C args (head MM) = C' -> 
      SubtraceWithSuffix cm C MM C' MM' MMO
  | SubSufNotNow: forall C C' MM MM' MMO M,
      (forall args, ~ isCall cm (head MM) args) -> 
      SubtraceWithSuffix cm C MM C' MM' MMO ->
      SubtraceWithSuffix cm C (notfinished M MM) C' MM' MMO
  | SubSufSkipCall : forall C C' MM MMskip MM' MM'' MMO args,
      isCall cm (head MM) args -> 
      TraceSpan (fun M => ~ (isRet (head MM) M)) MM MMskip (Some MM')  -> 
      SubtraceWithSuffix cm C MM' C' MM'' MMO ->
      SubtraceWithSuffix cm C MM C' MM'' MMO.
(* APT: This should be reverted like Subtrace so that we get all sub-traces, not just immediate children of the parent trace. *)

(* APT: Or, here's the following suggestion for restructing Subtrace and friends:
- Subtrace should just pick out the suffixes that start with a return.
- Users of Subtrace that need to use LongestPrefix or Span can do so themselves,
  avoiding the need for a separate SubtraceWithSuffix.
*)

(* Since eager property protects everything that is HI,
   an integrity rollback restores all HI components. *)
Definition RollbackInt (C: Contour) (Mstart Mend : MachineState) : MachineState :=
  fun k => match integrityOf (C k) with
           | HI => Mstart k
           | _ => Mend k
           end.

(* Observable properties take a contour and a trace, with an optional additional trace.
   The contour C represents the security levels for trace MM, and MMOouter is the
   execution following after MM when C no longer applies. *)
Definition ObservableIntegrity (C:Contour) (MM:MTrace) (MMsuffO:option MTrace) : Prop :=
 match MMsuffO with
 | Some actual =>
   let ideal := traceOf (RollbackInt C (head MM) (head actual)) in
   TracePrefix (ObsTraceOf ideal) (ObsTraceOf actual)
 | None => True
 end.
(* APT: Need a prefix analog to ObsTraceEq, to cope with stuttering? *)


(* A confidentiality rollback aims to undo a variation, so it restores the values of the
   original, unvaried state. But if the varied values were overwritten after they were varied,
   the changes should be kept. Otherwise we are building in some integrity. *)
Definition RollbackConf (Mstart Nstart Nend : MachineState) : MachineState :=
  fun k => if weq (Nstart k) (Nend k) && negb (weq (Mstart k) (Nstart k))
           then Mstart k
           else Nend k.

Definition ObservableConfidentiality (C:Contour) (MM:MTrace) (MMsuffO:option MTrace) (isRet:MachineState -> Prop) : Prop :=
  forall N NN NNO, variantOf (head MM) N C ->
                   TraceSpan (fun N' => ~ (isRet N')) (traceOf N) NN NNO ->
                   let actual := MM ^ MMsuffO in
                   let variant := NN ^ (option_map (fun NN => traceOf (RollbackConf (head MM) N (head NN))) NNO) in
                   TraceEq (ObsTraceOf variant) (ObsTraceOf actual).
(* APT: Modify to use ObsTraceEq? *)
(* APT: There is no real need to pass MMsuffO separately here; could just do the append
        in the caller. *)

Definition LazyStackSafety (cm : CallMap) (C:Contour) (MM:MTrace) : Prop :=
  ObservableIntegrity C MM None (* APT: This is superfluous *) /\
  ObservableConfidentiality C MM None (fun _ => False) /\
  (forall MM' C' MMsuffO, SubtraceWithSuffix cm C MM C' MM' MMsuffO ->
                          ObservableIntegrity C' MM' MMsuffO /\
                          ObservableConfidentiality C' MM' MMsuffO (isRet (head MM'))).

(* More conjectural stuff follows. *)

(* This is meant to rollback in all of the cases that either an integrity or a confidentiality
   rollback would. If a component is HI, it should always be rolled back; if HC but LI, it
   should be rolled back only if it kept the value of its variant. *)
Definition RollbackCI (C: Contour) (Mstart Nstart Nend : MachineState) : MachineState :=
  RollbackInt C Mstart (RollbackConf Mstart Nstart Nend).

Definition ObservableConfidentegrity (C:Contour) (MM:MTrace) (MMsuffO:option MTrace) (isRet:MachineState -> Prop) : Prop :=
  forall N NN NNO,
    variantOf (head MM) N C ->
    TraceSpan (fun N' => ~ isRet N') (traceOf N) NN NNO ->
    let actual := MM ^ MMsuffO in
    let ideal := NN ^ (option_map (fun NN' => traceOf (RollbackCI C (head MM) N (head NN'))) NNO) in
    TracePrefix (ObsTraceOf ideal) (ObsTraceOf actual).
(* APT: Again, need a prefix analog to ObsTraceEq, to cope with stuttering? *)

Definition LazyStackSafety' (cm : CallMap) (C:Contour) (MM:MTrace) : Prop :=
  ObservableConfidentegrity C MM None (fun _ => False) /\
  (forall MM' C' MMsuffO, SubtraceWithSuffix cm C MM C' MM' MMsuffO ->
                          ObservableConfidentegrity C' MM' MMsuffO (isRet (head MM'))).

Conjecture EagerSafetyImpliesLazy :
  forall cm C MM,
  EagerStackSafety cm MM C -> LazyStackSafety cm C MM.

Conjecture Lazy'ImpliesLazy :
  forall cm C MM,
  LazyStackSafety' cm C MM -> LazyStackSafety cm C MM.

Conjecture LazyNotImpliesLazy' :
  exists cm C MM,
  LazyStackSafety cm C MM /\ ~ LazyStackSafety' cm C MM.
(* The counterexample:

main: mov #0 r1
      store r1 FP
      [call sequence to sub]
      ld FP r1
      bne r1 r2 #2
      mov #1 O
      beq #0 #0 #1
      mov #0 O
      halt

sub:  ld (FP-1) r2
      beq r2 #0 #2
      mov #1 r1
      store r1 (FP-1)
      [return sequence]

In observable confidentiality, if the variation keeps main's memory the same,
sub returns and the behavior is [1]. Of course that is the case for the actual trace as well.
If it changes, sub writes 1 to it and to r1, so the behavior is still [1].

In observable integrity, sub never does anything, because there is no variant. So
the behavior is [1] for both the ideal and actual traces.

But for confidentegrity, if main's memory varies, sub moves 1 to r1 and stores it
in main's memory. Then the rollback sets main's memory back to 0. So r1 and r2 will
not be equal, and the behavior is [0]. So confidentegrity does not hold. *)

(* ********* Tags and tagged properties and policies ********* *)

(* Type of tags and some tags of interest, with a minimalist form of blessed
   call and return sequences.

   RB: TODO: Concretize this? Share among related sections? *)
Variable Tag : Type.
Variable Instr : Tag.
Variable Call : Tag.
Variable Ret : Tag.
Variable PCdepth : nat -> Tag.
Variable SPtag : Tag.
Variable Stack : nat -> Tag.
Variable H1 : Tag.

Section EagerPolicy.

(* Machine states are enriched with mappings from components to tags. (Should a
   rich state be a pair of a machine state and the enrichment?) For now, lists
   are used in lieu of sets and an ordering assumed.

   RB: TODO: Previously called RichState, harmonize w.r.t. testing development.
*)
Definition TagState := Component -> list Tag.
Variable tagsOf : TagState -> Component -> list Tag.

(* Given a call map [cm] and contour [C], relate these to the rich state(s) [T]
   whose tagging is compatible with those. (Add an initial machine state?) *)
Variable InitialTags : CallMap -> Contour -> TagState -> Prop.

(* We need some way to update tags. *)
Variable updateTag : TagState -> Component -> list Tag -> TagState.

(* We need to know whether the currently executing instruction performs memory
   operations (loads and stores), and on which address they operate. *)
Variable isLoad : MachineState -> Addr -> Prop.
Variable isStore : MachineState -> Addr -> Prop.

CoInductive TaggedStep (M: MachineState) (T : TagState) : TagState -> Prop :=
| TCall : forall T' d,
    tagsOf T (Mem (M (Reg PC))) = [Call; Instr] ->
    tagsOf T (Reg PC) = [PCdepth d] ->
    updateTag T (Reg PC) [PCdepth (S d)] = T' ->
    TaggedStep M T T'
| TRet : forall T' d,
    tagsOf T (Mem (M (Reg PC))) = [Instr; Ret] ->
    tagsOf T (Reg PC) = [PCdepth (S d)] ->
    updateTag T (Reg PC) [PCdepth d] = T' ->
    TaggedStep M T T'
| TLoad : forall iaddr dPC dMem,
    isLoad M iaddr ->
    tagsOf T (Reg PC) = [PCdepth dPC] ->
    tagsOf T (Mem iaddr) = [Stack dMem] ->
    dPC <= dMem ->
    TaggedStep M T T
| TStore : forall T' iaddr d,
    isStore M iaddr ->
    tagsOf T (Reg PC) = [PCdepth d] ->
    updateTag T (Mem iaddr) [Stack d] = T' ->
    TaggedStep M T T'
(* ... *)
.

CoInductive TaggedRun : TagState -> MTrace -> Prop :=
| RunFinished : forall T M,
    TaggedRun T (finished M)
| RunNotfinished : forall T T' M MM O,
    step M = Some (head MM,O) ->
    TaggedStep M T T' ->
    TaggedRun T' MM ->
    TaggedRun T (notfinished M MM).

(* TODO: Add missing ingredients from testing and important details. *)

(* The eager policy allows a trace if said trace can result from a run of the
   rich machine starting from the initial enriched state. *)
CoInductive EagerPolicyTrace : CallMap -> Contour -> MTrace -> Prop :=
| EPTIntro : forall cm C T MM,
    InitialTags cm C T ->
    TaggedRun T MM ->
    EagerPolicyTrace cm C MM.

Conjecture EagerPolicy_StackSafety :
  forall cm MM C,
    EagerPolicyTrace cm C MM ->
    EagerStackSafety cm MM C.

End EagerPolicy.

Section EagerTestingProperty.

(* TODO: Consider moving towards a computable variant of the property. *)

(* The state of the PIPE is a tag map and a counter containing the next unique
   identifier to be generated. *)
Definition PipeState := (TagState * nat)%type.

(* The rich machine state is simply a pair of machine and PIPE states. *)
Definition RichState := (MachineState * PipeState)%type.

(* Simplified state description "tags" for the testing property. *)
Variant DescTag :=
| DTStack : nat -> DescTag
| DTInstr : DescTag
| DTOther : DescTag.

(* State description for the testing policy. *)
Record StateDesc := mkStateDesc {
  pcdepth : nat ;
  memdepth : Addr -> DescTag ;
  dstack : list (Addr * Addr * RichState) ;
  callinstrs : list Addr ;
  callsites : list Addr ;
}.

(* Tag helpers. *)
Definition callTag := [Call; Instr]. (* Should be "callerTag"? *)
Definition calleeTag := [H1; Instr].
(* From tag sets to description "tags". *)
Variable to_desc : list Tag -> DescTag.
  (* match ts with *)
  (* | [Stack n] => DSStack n *)
  (* | [PCdepth _] => DTOther *)
  (* | [SPtag] => DTOther *)
  (* | _ => DTInstr *)
  (* end. *)
(* These would be standard map and filter functions on finite memories. *)
Variable map : forall {A B C : Type} (m : A -> B) (f : B -> C), (A -> C).
Variable eqMap : forall {A B : Type} (m1 m2 : A -> B) (def : B -> Prop), Prop.
Variable mapFilter :
  forall {A B : Type} (m : A -> B) (f : A -> B -> Prop), (A -> B).

Arguments eqMap {_ _} _ _ _.
Arguments mapFilter {_ _} _ _ _.

Definition eqMapFilter {A B} (m1 m2 : A -> B) f d :=   
  eqMap (mapFilter m1 f) (mapFilter m2 f) d.
(* More helpers for memories. *)
Variable memLayout : TagState -> (Addr -> DescTag).
Variable memCallers : TagState -> list Addr.
Variable memCallees : TagState -> list Addr.
(* And some more. *)
Variable stateMem : RichState -> (Addr -> Value).
Variable defMem : Value.

(* Default memory tag. *)
Definition initMem := [Stack 0].
Definition defDesc := to_desc initMem.

(* Initial state description. *)
Definition initDesc (ts : TagState) : StateDesc :=
  mkStateDesc
    0
    (memLayout ts)
    []
    (memCallers ts)
    (memCallees ts).

(* Test state as state of the main machine and a list of variant machines with
   their states. *)
Definition TestState := (RichState * list RichState)%type.

(* Attempt to take a step in all machine variants. *)
Variable testStep : TestState -> option TestState.

(* Helpers for single-step stack safety. *)
Definition tagOf (def : DescTag) (addr : Addr) (sd : StateDesc) : DescTag :=
  (memdepth sd) addr. (* Not using the default here, vs. sparse memory maps. *)

Definition accessibleTag (t : DescTag) (depth : nat) : Prop :=
  match t with
  | DTStack n => n >= depth
  | DTInstr => False
  | DTOther => False
  end.

Definition isAccessible (def : DescTag) (addr : Addr) (sd : StateDesc) : Prop :=
  accessibleTag (tagOf def addr sd) (pcdepth sd).

Definition isInaccessible (def : DescTag) (addr : Addr) (sd : StateDesc) : Prop :=
  ~ accessibleTag (tagOf def addr sd) (pcdepth sd).

Definition isInstruction (def : DescTag) (addr : Addr) (sd : StateDesc) : Prop :=
  match (tagOf def addr sd) with
  | DTInstr => True
  | _ => False
  end.

(* single_step_stack_safety *)
Inductive EagerTestingSingleStep
           (s  : RichState)
           (d  : StateDesc)
           (t  : RichState) (* variant of [s] w.r.t. [d] *)
           (s' : RichState) (* state such that [s] steps to it *)
           (d' : StateDesc) (* state description of [s'] *)
           (t' : RichState) (* state such that [t] steps to it *)
  : Prop :=
| ETsingle :
    (* Instruction memory of [s'] and [t'] w.r.t. [d] agrees. *)
    let isInstruction' addr _ := isInstruction defDesc addr d in
    eqMapFilter (stateMem s') (stateMem t') isInstruction' (fun _ => False) ->
    (* Accessible memory of [s'] and [t'] w.r.t. [d] agrees. *)
    let isAccessible' addr _ := isAccessible defDesc addr d in
    eqMapFilter (stateMem s') (stateMem t') isAccessible' (fun x => x = defMem) ->
    (* Inaccessible memory of [t] and [t'] w.r.t. [d] agrees. *)
    let isInaccessible' addr _ := isInaccessible defDesc addr d in
    eqMapFilter (stateMem t) (stateMem t') isInaccessible' (fun x => x = defMem) ->
    (* The step eagerly satisfies stack safety. *)
    EagerTestingSingleStep s d t s' d' t'.

(* next_state *)
Variable next_desc :
  forall (def : DescTag) (s : RichState) (d : StateDesc) (s' : RichState),
  option StateDesc.

(* prop_stack_safety_full (1)
   (1) works on genVariationTestState (2)
       and uses to_desc, callTag and calleeTag to get initDesc
       and passes this to stack_safety_full (3)
   (2) takes a few arguments for generation, including isSecretMP (4)
       leaving this abstract at the moment
   (3) operates on traces of TestStates (Main + Variants) *)
(* TODO: Synchronize MTrace and TestState. *)
CoInductive EagerTestingFull : MTrace -> StateDesc -> TestState -> Prop :=
| ETFdone : forall M d ts,
    EagerTestingFull (finished M) d ts
| ETFstep : forall M MM dInput dUpdated tsInput tsScrambled tsStepped,
    (* First, check if the currently executed instruction is (the destination
       of) a call. If it is, scramble. *)
    (* In (M (Reg PC)) (callsites d) -> *)
    (* Take a step in all machine variants. *)
    testStep tsScrambled = Some tsStepped ->
    (* Compute the next state description. *)
    next_desc defDesc (fst tsInput) dInput (fst tsStepped) = Some dUpdated ->
    (* Call single-step stack safety for each variant.*)
    (* ... *)
    EagerTestingFull (notfinished M MM) dInput tsInput.

Variable EagerTesting : Prop.

(* Conjecture EagerTesting_StackSafety : ... *)

End EagerTestingProperty.

End foo.

(*
(* Following attempts to encode subtraces that start on transition to NOTME, but can end anywhere as long as still NOTME. 
There is surely still a prettier way! *)


Definition notme (id: Identity) : Prop :=
  match id with
  | NOTME _ _ _ _ => True
  | _ => False
  end.

Definition notme' (cid : Contour * Identity * MachineState) := notme (snd (fst cid)).

CoInductive subtraceAux : CTrace -> MTrace -> Contour -> Prop :=
| subtraceAuxNow: forall C id m MM MM',
     ~ notme id -> TracePrefix MM MM' -> ForallTrace notme' MM' -> subtraceAux (notfinished (C,id,m) MM) (mapTrace snd MM') C
| subtraceAuxLater: forall cim C MM MM' ,  subtraceAux MM MM' C -> subtraceAux (notfinished cim MM) MM' C
.
                                                                      
Definition subtrace (retSP: Value) (cm :CallMap) (C0: Contour) (super: MTrace) (sub: MTrace) (C:Contour) :=
  subtraceAux (CTraceOf retSP C0 super cm) sub C.


(* APT: As things stand, retSP is always initSP.  Is this right? *)
(* LEO: The retSP should always be the stack pointer of the callee of the "initial" process. So when recursing in StackSafety the retSP should be the SP of (head Mcallee) I think. *)
(* APT: Does the adjustment below do the trick? *)

End foo.


(* There are many well-formedness conditions on this... *)
  
Inductive Identity :=
| ME : Value -> (* SP below which I can't access things *) 
       Identity
| NOTME : Value -> (* PC at the time of call *)
          Value -> (* SP at the time of call *)
          nat -> (* local state size *)
          Value -> (* SP of callee *)
          Identity 
| TRANS :
    list Value -> (* Instructions remaining in the sequence *)
    nat ->        (* local state size to be allocated *)
    Value ->      (* PC at the time of call *)
    Value ->      (* SP at the time of call *)
    Value ->      (* SP of callee *)
    Identity.

Definition ITrace := Trace (Identity * MachineState).

(* APT: Recast as operator over MTraces.
        Assumes each call sequence starts with the JAL, right? 
        Is this essential, or was it just to make things a bit simpler? *)
(* LEO: Each call sequence starts with a jal : that makes the
formalization significantly simpler as you can figure out the
information you need for contour changes the moment you start the
transition. Is it too unrealistic an assumption? *)
(* APT: I think this is fine, provided that we allow the callee to
access the piece of the caller’s stack containing the arguments. To do
this, we can add an additional parameter to the call map entries
giving the number of args.  (Note that this prevents our handling
dynamic frame sizes, but that is a feature that is ok to omit at least
at first.)  *) 
(* LEO: Note that this way the handling of arguments/returns is not
part of the blessed sequence. And we could either (1) assume there is
enough local stack space for all calls or (2) handle stack allocation
and deallocation in the contours.  *)

CoFixpoint ITraceOfAux (id : Identity) (MM : MTrace) (M: MachineState) (cm : CallMap) : ITrace :=
  match MM with
  | finished _ => finished (id, M)
  | notfinished _ MM' => 
    let M' := head MM' in
    match id with
    | ME meSP =>
      match find (fun cme =>
                    match cme with
                    | (h::_, _) => valueEq h (valueOf PC M')
                    | _ => false
                    end) cm with
      | Some (seq, sz) =>
        notfinished (id,M) (ITraceOfAux (TRANS seq
                                               sz 
                                               (valueOf PC M')
                                               (valueOf SP M')
                                               meSP)
                                        MM' M' cm)
      | None =>
        notfinished (id,M) (ITraceOfAux (ME meSP) MM' M' cm)
      end
    | TRANS seq sz jalPC jalSP meSP =>
      match seq with
      | _im :: im' :: ims =>
        notfinished (id,M)
                    (ITraceOfAux (TRANS (im' :: ims) sz jalPC jalSP meSP) MM' M' cm)
      | _ =>
        (* Potential check: should be a singleton list always (_im) *)
        notfinished (id, M)
                    (ITraceOfAux (NOTME jalPC jalSP sz meSP) MM' M' cm)
      end
    | NOTME jalPC jalSP sz meSP => 
      if andb (valueEq (valueOf PC M') (vplus jalPC 4))
              (valueEq (valueOf SP M') jalSP) then
        notfinished (id,M) (ITraceOfAux (ME meSP) MM' M' cm)
      else
        notfinished (id,M) (ITraceOfAux (NOTME jalPC jalSP sz meSP) MM' M' cm)
    end
  end.

Definition CTrace := Trace (Contour * Identity * MachineState).

Definition updateContour (C : Contour) (id id' : Identity) (M M' : MachineState) :=
  match id, id' with
  | ME _, ME _ => C
  | NOTME _ _ _ _, NOTME _ _ _ _ => C
  | TRANS _ _ _ _ _, TRANS _ _ _ _ _ => C
  | ME _, TRANS _ sz _ _ _=>
    (* Everything other than the sz top parts of the stack becomes unreachable. *)
    fun k => if cle k (componentOf (vminus (valueOf SP M) sz))
             then (HC, HI) else C k
  | TRANS _ _ _ _ _, NOTME _ jalSP _ _=>
    (* Everything between the size of SP at the call, and the current SP 
       is now "local state" *)
    fun k => if andb (cle k (componentOf (valueOf SP M')))
                     (clt (componentOf jalSP) k)
             then (LC, LI)
             else C k
  | NOTME _ _ (* jalSP *) _ _, ME meSP =>
    (* Everything above the SP at the call becomes unreadable again,
       Everything below the SP but above the low limit of ME becomes
       readable again. *)
    fun k => if andb (clt (componentOf meSP) k)
                     (cle k (componentOf (valueOf SP M')))
             then (LC, LI)
             else if clt (componentOf (valueOf SP M')) k then (HC, HI)
             else C k
  | _, _ => (* ERROR CASE *)
    C 
  end.    

CoFixpoint ContouredTraceOf (C : Contour) (it : ITrace) :=
  match it with
  | finished (id, M) =>
    finished (C, id, M)
  | notfinished (id, M) MM =>
    let (id', M') := head MM in
    let C' := updateContour C id id' M M' in
    notfinished (C, id, M) (ContouredTraceOf C' MM)
  end.

Definition CTraceOf (retSP : Value) (C : Contour) (MM : MTrace) (cm : CallMap) :=
  ContouredTraceOf C (ITraceOfAux (ME retSP) MM (head MM) cm).


Definition updateObs (s : StateObs) (C' : Contour) (M' : MachineState) : StateObs :=
  fun k => match confidentialityOf (C' k) with
           | LC => Some (valueOf k M')
           | HC => s k
           end.

CoFixpoint ObsTraceAux (s : StateObs) (ct : CTrace) : OTrace :=
  match ct with
  | finished (C, id, M) =>
    finished (updateObs s C M)
  | notfinished (C, id, M) CIMs =>
    let s' := updateObs s C M in
    notfinished s' (ObsTraceAux s' CIMs)
  end.
  
Definition ObsTrace (ct : CTrace) : OTrace :=
  let '(C,_,M) := head ct in
  let s0 := fun k =>
              match confidentialityOf (C k) with
              | LC => Some (valueOf k M)
              | HC => None
              end in
  ObsTraceAux s0 ct.


*)
