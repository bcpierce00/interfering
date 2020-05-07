Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.

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
Variable step : MachineState -> MachineState * Observation.

Variable PolicyState : Type.
Variable pstep : MachineState * PolicyState -> option PolicyState.
(* TODO: CallMap as an argument? *)
Variable initPolicyState : MachineState -> PolicyState.

Definition MPState : Type := MachineState * PolicyState.

Definition ms (mp : MPState) := fst mp.
Definition ps (mp : MPState) := snd mp.

Definition mpstep (mp : MPState) :=
  let (m', O) := step (ms mp) in
  match pstep mp with
  | Some p' => Some (m', p', O)
  | None => None
  end.

(*******************)
(***** Traces ******)
(*******************)

CoInductive TraceOf (A : Type) : Type :=
| finished : A -> TraceOf A
| notfinished : A -> TraceOf A -> TraceOf A.

Arguments finished {_} _.
Arguments notfinished {_} _ _.

Definition idTrace {A} (MM: TraceOf A) : TraceOf A :=
  match MM with
  | finished M => finished M
  | notfinished M MM' => notfinished M  MM'
  end.

Lemma idTrace_eq : forall {A} (MM: TraceOf A), MM = idTrace MM.
   destruct MM; reflexivity.
Qed.

Definition head {A} (MM : TraceOf A) : A :=
  match MM with
  | finished M => M
  | notfinished M _ => M
  end.

Inductive InTrace {A} (m:A) : TraceOf A -> Prop :=
| In_finished : InTrace m (finished m)
| In_now : forall MM, InTrace m (notfinished m MM)
| In_later : forall m' MM, InTrace m MM -> InTrace m (notfinished m' MM).

Lemma head_InTrace :forall {A} (MM: TraceOf A), InTrace (head MM) MM.
Proof.
  intros.
  destruct MM.
  - constructor.
  - simpl. constructor.
Qed.

CoFixpoint mapTrace {A B:Type} (f:A -> B) (MM: TraceOf A) : TraceOf B :=
  match MM with
  | finished M => finished (f M)
  | notfinished M MM' => notfinished (f M) (mapTrace f MM')
  end.

CoInductive ForallTrace {A:Type} (P:A -> Prop) : TraceOf A -> Prop :=
| Forall_finished : forall M, P M -> ForallTrace P (finished M)
| Forall_notfinished : forall M MM', P M -> ForallTrace P MM' -> ForallTrace P (notfinished M MM')
.

CoInductive TraceEq {A} : TraceOf A -> TraceOf A -> Prop :=
| EqFin : forall m, TraceEq (finished m) (finished m)
| EqCons : forall m mm1 mm2, TraceEq mm1 mm2 ->
                             TraceEq (notfinished m mm1) (notfinished m mm2).

CoFixpoint TraceApp {A} (MM: TraceOf A) (MMO: option (TraceOf A)) : TraceOf A :=
  match MM with
  | finished m =>
    match MMO with
    | Some m' => notfinished m m'
    | None => MM
    end
  | notfinished m MM' => notfinished m (TraceApp MM' MMO)
  end.

Notation "MM1 ^ MM2" := (TraceApp MM1 MM2).

Definition OptTraceApp {A} (MMO1: option (TraceOf A)) (MMO2: option (TraceOf A)) : option (TraceOf A) :=
  match MMO1 with
  | Some MM => Some (TraceApp MM MMO2)
  | None => MMO2
  end.

Notation "MM1 ?^ MM2" := (OptTraceApp MM1 MM2) (at level 80).

Lemma TraceAppHead {A} :
  forall (MM NN : TraceOf A) (NNO : option (TraceOf A)),
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
CoInductive TracePrefix {A} : TraceOf A -> TraceOf A -> Prop :=
| PrefixEq  : forall m, TracePrefix (finished m) (finished m)
| PrefixNow : forall m mm, TracePrefix (notfinished m mm) (finished m)
| PrefixLater : forall m mm1 mm2, TracePrefix mm1 mm2 ->
                                  TracePrefix (notfinished m mm1)
                                              (notfinished m mm2).

Notation "MM2 <<== MM1" := (TracePrefix MM1 MM2) (at level 80).

(* Divide MM1 into MM2 ++ MMO such that MM2 is the longest prefix for which P holds on each element *)
Definition TraceSpan {A} (P : A -> Prop) (MM1 MM2 : TraceOf A) (MMO : option (TraceOf A)) : Prop :=
  MM1 = MM2^MMO /\ ForallTrace P MM2 /\
  forall MM2', MM2' <<== MM1 ->
    ForallTrace P MM2' ->
    MM2' <<== MM2.

(* MM2 is the longest prefix of MM1 for which P holds on each element. *)
Definition LongestPrefix {A} (P : A -> Prop) (MM1 MM2 : TraceOf A) : Prop :=
  exists MMO, TraceSpan P MM1 MM2 MMO.

Inductive IsEnd {A} : TraceOf A -> A -> Prop :=
| IsEndNow : forall M, IsEnd (finished M) M
| IsEndLater : forall MM M M', IsEnd MM M -> IsEnd (notfinished M' MM) M
.

(* Definition tail {A} (MM: TraceOf A) : option (TraceOf A) := *)
(*   match MM with *)
(*   | finished _ => None *)
(*   | notfinished _ M => Some M *)
(*   end. *)

(* Fixpoint ith {A} (i:nat) (MM: TraceOf A) : option A := *)
(*   match i with *)
(*   | O => Some (head MM) *)
(*   | S i' => match tail MM with *)
(*             | Some MM' => ith i' MM' *)
(*             | None => None                               *)
(*             end *)
(*   end. *)

(* Lemma head_ith : forall {A} (MM: TraceOf A), ith O MM = Some (head MM). *)
(* Proof. *)
(*   destruct MM. *)
(*   - auto. *)
(*   - auto. *)
(* Qed. *)

(* todo: Rename MPState to State and MPTrace to Trace, mp -> t *)
Definition MTrace := TraceOf MachineState.

CoFixpoint MTraceOf (M : MachineState) : MTrace :=
  notfinished M (MTraceOf (fst (step M))).

Definition MPTrace := TraceOf MPState.

CoFixpoint MPTraceOf (mp : MPState) : MPTrace :=
  match pstep mp with
  | None => finished mp
  | Some p' => notfinished mp (MPTraceOf (fst (step (ms mp)), p'))
  end.


(* LEO: TODO: Add well formedness that a MTrace/MPTrace is compatible with the steps. *)

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
Definition EagerStackIntegrity (C : Contour) (MP: MPTrace) : Prop :=
    forall (k: Component), integrityOf (C k) = HI ->
      forall (mp : MPState),
        InTrace mp MP -> ms (head MP) k = ms mp k.

(* CoInductive variant *)
CoInductive EagerStackIntegrity' (C : Contour) : MPTrace -> Prop :=
| SI_finished : forall mp, EagerStackIntegrity' C (finished mp)
| SI_notfinished :
    forall (mp: MPState) (MP : MPTrace),
    (forall (k: Component), integrityOf (C k) = HI -> ms mp k = ms (head MP) k) ->
    EagerStackIntegrity' C MP ->
    EagerStackIntegrity' C (notfinished mp MP).

Lemma StackIntegrityEquiv : forall (C:Contour) (MP: MPTrace),
     EagerStackIntegrity C MP -> EagerStackIntegrity' C MP.
Proof.
  cofix COFIX.
  intros.
  destruct MP.
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

Lemma StackIntegrity'Equiv : forall (C:Contour) (MP: MPTrace),
     EagerStackIntegrity' C MP -> EagerStackIntegrity C MP.
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

(* NB: It doesn't matter whether we calculate this at a
call instruction (as in a subtrace) or at the first
instruction of the callee (as in the top-level trace)
assuming that registers remain LI,LC at all times. *)

Definition variantOf (M N : MachineState) (C : Contour) :=
  forall (k : Component), confidentialityOf (C k) = LC ->
                          M k = N k.

Definition ObsTrace := TraceOf Observation.

CoFixpoint ObsTraceOfM (M: MTrace) : ObsTrace :=
  match M with
  | finished m =>
    finished Tau
  | notfinished m M' =>
    let (m', O) := step m in
    notfinished O (ObsTraceOfM M')
  end.

CoFixpoint ObsTraceOf (MP: MPTrace) : ObsTrace :=
  match MP with
  | finished mp =>
    finished Tau
  | notfinished mp MP' =>
    let (m', O) := step (ms mp) in
    notfinished O (ObsTraceOf MP')
  end.
(*                
    match pstep mp with
    | Some p' =>
      notfinished O (ObsTraceOf MP')
    | None => (* This should never happen in a valid MPTrace *)
      finished O
    end
*)

(* TODO: If MPTrace is well formed, then it is a prefix of the induced one *)

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

CoInductive ObsTraceEq : TraceOf Observation -> TraceOf Observation -> Prop :=
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

Definition ObsTracePrefix (OO OO' : TraceOf Observation) : Prop :=
  exists OO'', ObsTraceEq OO OO'' /\ OO' <<== OO'' \/ ObsTraceEq OO' OO'' /\ OO' <<== OO.

(* SNA: I have made this include the return to match lazy better. *)
Definition EagerStackConfidentiality (C : Contour) (MP : MPTrace) (isRet : MachineState -> Prop) :=
  forall m' M',
    variantOf (ms (head MP)) m' C ->
    LongestPrefix (fun m => isRet m -> IsEnd (mapTrace fst MP) m) M' (MTraceOf m') ->
    ObsTraceEq (ObsTraceOf MP) (ObsTraceOfM M') /\
    ((exists mpret, IsEnd MP mpret) <-> (exists mret', IsEnd M' mret')) /\
    (forall mpret mret' k,
      IsEnd MP mpret -> IsEnd M' mret' ->
      ms (head MP) k <> ms mpret k \/ (head M') k <> mret' k ->
      ms mpret k = mret' k).

(* Old, not co-terminating formalization: 
    (IsEnd MP mpret -> exists mret', IsEnd M' mret' /\
                 forall k,
                 ms (head MP) k <> ms mpret k \/ (head M') k <> mret' k ->
                 ms mpret k = mret' k).

*)

CoInductive StrongEagerStackConfidentiality (R : MachineState -> Prop) :
  MPTrace -> MTrace -> Prop :=
| StrongConfStep :
    (* Maybe the top one should have a not ret *)
    forall mp MP m' M' O,
      mpstep mp = Some (ms (head MP), ps (head MP), O) ->
      step m' = (head M', O) ->
      (forall k, ms (head MP) k <> ms mp k \/
                 (head M') k <> m' k -> ms (head MP) k = head M' k) ->
      StrongEagerStackConfidentiality R MP M' ->
      StrongEagerStackConfidentiality R (notfinished mp MP) (notfinished m' M')
| StrongConfEnd :
    forall mp m,
      R (ms mp) -> R m ->
      StrongEagerStackConfidentiality R (finished mp) (finished m).

Lemma confStepPreservesVariant :
  forall C mp m' p' OM mv mv' ON,
    mpstep mp = Some (m', p', OM) ->
    step mv = (mv', ON) ->
    (forall k, m' k <> ms mp k \/ mv' k <> mv k -> m' k = mv' k) ->
    variantOf (ms mp) mv C ->
    variantOf m' mv' C.
Proof.
  unfold variantOf.
  intros C mp m' p' OM mv mv' ON StepM StepN Conf Var k Hk.
  destruct (WordEqDec (m' k) (ms mp k)) as [eqM | neqM];
  destruct (WordEqDec (mv' k) (mv k)) as [eqN | neqN];
  try solve [ apply Conf; auto ];
  rewrite eqM; rewrite eqN; auto.
Qed.

Lemma StrongConfImpliesObsEq :
  forall C R MP MV,
    variantOf (ms (head MP)) (head MV) C ->
    StrongEagerStackConfidentiality R MP MV ->
    ObsTraceEq (ObsTraceOf MP) (ObsTraceOfM MV).
Proof.
  cofix COFIX.
  intros C R MP MV Var Conf.
  inversion Conf; simpl.
  - match goal with
    | [ |- ObsTraceEq ?T1 ?T2 ] =>
      rewrite (idTrace_eq T1); rewrite (idTrace_eq T2); simpl
    end.
    repeat match goal with
           | [ H : step ?M = _ |- context[step ?M] ] => rewrite H; simpl
           end.
    unfold mpstep in *.
    destruct (step (ms mp)) eqn:HStepMP.
    destruct (pstep mp) eqn:HPStepMP; inversion H.
    destruct O.
    + apply ObsEqNow.
      eapply COFIX; eauto.
      eapply confStepPreservesVariant; eauto.
      * unfold mpstep. rewrite HStepMP. rewrite HPStepMP.
        subst.
        eauto.
      * assert (head MP = mp) as HM
          by (destruct H3; auto).
        assert (head MV = m') as HN
          by (destruct H4; auto).
        rewrite <- HM.
        rewrite <- HN.  
        apply Var.
    + apply ObsEqTau1.
      apply ObsEqTau2.
      eapply COFIX; eauto.
      eapply confStepPreservesVariant; eauto.
      * unfold mpstep. rewrite HStepMP. rewrite HPStepMP.
        subst.
        eauto.
      * assert (head MP = mp) as HM
          by (destruct H3; auto).
        assert (head MV = m') as HN
          by (destruct H4; auto).
        rewrite <- HM.
        rewrite <- HN.
        apply Var.
  - match goal with
    | [ |- ObsTraceEq ?T1 ?T2 ] =>
      rewrite (idTrace_eq T1); rewrite (idTrace_eq T2); simpl
    end.
    apply ObsEqFinishedTau.
Qed.

Lemma ComponentConfTrans :
  forall (M0 M1 M2 N0 N1 N2 : MachineState),
    (forall k : Component, M1 k <> M0 k \/ N1 k <> N0 k -> M1 k = N1 k) ->
    (forall k : Component, M1 k <> M2 k \/ N1 k <> N2 k -> M2 k = N2 k) ->
    (forall k : Component, M0 k <> M2 k \/ N0 k <> N2 k -> M2 k = N2 k).
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

Lemma StrongConfImpliesCotermination :
  forall C R MP MV,
    variantOf (ms (head MP)) (head MV) C ->
    StrongEagerStackConfidentiality R MP MV ->
    (exists mpret, IsEnd MP mpret) <-> (exists mvret, IsEnd MV mvret).
Proof.
  intros C R MP MV Var Conf; split.
  - intros [mpret HEnd].
    generalize dependent MV.
    induction HEnd; subst; eauto; intros MV Var Conf;
    inversion Conf; subst; eauto; clear Conf; simpl in *.
    + exists m.
      constructor.
    + destruct (IHHEnd M'0); eauto using confStepPreservesVariant.
      exists x; constructor; eauto.
  - intros [mvret HEnd].
    generalize dependent MP.
    induction HEnd; subst; eauto; intros MP Var Conf;
    inversion Conf; subst; eauto; clear Conf; simpl in *.
    + exists mp.
      constructor.
    + destruct (IHHEnd MP0); eauto using confStepPreservesVariant.
      exists x; constructor; eauto.
Qed.

Lemma StrongConfImpliesEndConf :
  forall C R MP MV mpret mvret,
    variantOf (ms (head MP)) (head MV) C ->
    StrongEagerStackConfidentiality R MP MV ->
    IsEnd MP mpret -> IsEnd MV mvret ->
    forall k, ms (head MP) k <> ms mpret k \/ (head MV) k <> mvret k  ->
              ms mpret k = mvret k.
Proof.
  intros C R MP MV mpret mvret Var Conf HMPEnd HMVEnd.
  generalize dependent MV.
  generalize dependent mvret.
  induction HMPEnd; subst; eauto; intros mvret MV Var Conf HMVEnd;
    inversion Conf; subst; eauto; clear Conf; simpl in *.
  - intros k Hk.
    inversion HMVEnd; subst; clear HMVEnd; eauto.
    inversion Hk; exfalso; eauto.
  - inversion HMVEnd; subst; clear HMVEnd; eauto.
    eapply ComponentConfTrans; eauto.
    intros k Hk.
    eapply IHHMPEnd; eauto using confStepPreservesVariant.
Qed.    

Theorem StrongConfImpliesConf (C: Contour) (R: MachineState -> Prop) (MP : MPTrace) :
  (forall (MV : MTrace),
    variantOf (ms (head MP)) (head MV) C ->
    StrongEagerStackConfidentiality R MP MV) ->
  EagerStackConfidentiality C MP R.
Proof.
  intros Conf.
  intros mv MV HVar [MMO [App [NotR Pref]]].
  specialize (Conf MV).
  assert (head MV = mv) as HN.
  { apply TraceAppHead in App.
    rewrite App.
    simpl.
    destruct (step mv); simpl; auto.
  }
  split; [|split].
  - eapply StrongConfImpliesObsEq; eauto.
    + rewrite HN; eauto.
    + eapply Conf.
      rewrite HN; eauto.
  - eapply StrongConfImpliesCotermination; eauto.
    + rewrite HN; eauto.
    + eapply Conf; rewrite HN; eauto.
  - intros mpret mret k HMPEnd HMVEnd.
    eapply StrongConfImpliesEndConf; eauto.
    + rewrite HN; eauto.
    + eapply Conf.
      rewrite HN; eauto.
Qed.

Definition CallMap := Value -> nat -> Prop.

Definition isCall (cm: CallMap) (m: MachineState) (args: nat) : Prop :=
   cm (m (Reg PC)) args.

Definition isRet (mc m: MachineState) : Prop :=
  m (Reg PC) = wplus (mc (Reg PC)) 4 /\ m (Reg SP) = mc (Reg SP).

Definition updateContour (C: Contour) (args: nat) (m: MachineState) : Contour :=
  fun k =>
    match k with
    | Mem a =>
      let a' := wminus (m (Reg SP)) args in
      if wle a a' then
        (HC, HI)
      else if andb (wlt a' a) (wle a (m (Reg SP))) then
        (LC, LI)
      else if wlt (m (Reg SP)) a then
        (HC, LI)
      else C k (* impossible *)
    | _ => C k
    end.

(* SNA: Since we never actually use the old contour in updateContour,
   I made this for FindCall, below. (Importantly, if we did use the old contour,
   newer versions of subtrace would be wrong.) *)
Definition makeContour (args : nat) (m : MachineState) : Contour :=
  fun k =>
    match k with
    | Mem a =>
      let a' := wminus (m (Reg SP)) args in
      if wle a a' then
        (HC, HI)
      else if andb (wlt a' a) (wle a (m (Reg SP))) then
        (LC, LI)
      else (*if wlt (M (Reg SP)) a then*)
        (HC, LI)
    | _ => (LC, LI)
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
(* Make this "Make Contour" *)
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
      Subtrace cm C MM C' MM' ->
      Subtrace cm C (notfinished M MM) C' MM'.
*)
(* APT+SNA: rather than two subtraces, with and without suffix, we could just
   find the starts of calls and then take prefixes/suffixes when we need them.
   Also we don't really need to update contours so much as just generate them
   from the state. *)
CoInductive FindCall (cm: CallMap) : MTrace -> Contour -> MTrace -> Prop :=
  | FindCallNow : forall C MM MM' args,
      (* Current instruction is a call *)
      isCall cm (head MM) args ->
      (* Construct the contour *)
      makeContour args (head MM) = C ->
      FindCall cm MM C MM'
  | FindCallLater: forall C MM MM' M,
      (forall args, ~ isCall cm (head MM) args) ->
      FindCall cm MM C MM' ->
      FindCall cm (notfinished M MM) C MM'.

Definition FindCallMP (cm : CallMap) (MP : MPTrace) (C : Contour) (MP' : MPTrace) :=
  FindCall cm (mapTrace ms MP) C (mapTrace ms MP').

(* TODO: Write find call MP coinductively, prove equiv? *)

(*
CoInductive StackSafety (cm : CallMap) : MTrace -> Contour -> Prop :=
  ss : forall (MM : MTrace) (C : Contour),
       (StackIntegrity C MM) ->
       (StackConfidentiality C MM) ->
       (forall MM' C', Subtrace cm C MM C' MM' -> StackSafety cm MM' C') ->
       StackSafety cm MM C.
*)
Definition EagerStackSafety (cm : CallMap) : MPTrace -> Contour -> Prop :=
  fun (MP : MPTrace) (C : Contour) =>
    (EagerStackIntegrity C MP) /\
    (EagerStackConfidentiality C MP (fun _ => False)) /\
    (forall (MPpre' MP' : MPTrace) C',
        FindCallMP cm MP C' MP' -> (* Find call*)
        LongestPrefix (fun mp => ~ (isRet (ms (head MP)) (ms mp))) MP' MPpre' ->
        EagerStackIntegrity C' MPpre' /\
        EagerStackConfidentiality C' MPpre' (isRet (ms (head MPpre')))).

(* TODO: step by step property that implies the rest *)

(* TODO: Rename this to SafeTrace or something, then write StackSafe
   as a top-level property that either quantifies over all traces (for
   a dynamic analysis) or only over a subset (e.g., those produced by
   a stack-protecting compiler). *)

(***** TESTING Property **********)
(* Note: This enforces lockstep due to PC equality.
   TODO: How not to enforce lockstep? *)

Definition EagerIntegrityTest (C : Contour) (M M' : MachineState) : Prop :=
  forall (k : Component), integrityOf (C k) = HI -> M k = M' k.

Definition EagerConfidentialityTest (isRet : MachineState -> Prop)
           (M M' N N' : MachineState) (OM ON : Observation) : Prop :=
  OM = ON /\
  forall (k : Component),  M k <> M' k \/ N k <> N' k -> M' k = N' k.

(* Elements of the Variant Stack. *)
Record VSE := {
  init_machine : MachineState;
  init_variant : MachineState;
  curr_variant : MachineState;
  contour : Contour;
  retP : MachineState -> Prop
}.

Definition upd_curr (mv : MachineState) (vse : VSE) : VSE :=
  {| init_machine := init_machine vse;
     init_variant := init_variant vse;
     curr_variant := mv;
     contour := contour vse;
     retP := retP vse
  |}.

Inductive VSE_step : VSE -> VSE -> Prop :=
| vse_step :
    forall m0 mv0 mv mv' C R,
    (exists O, step mv = (mv', O)) ->
    VSE_step (Build_VSE m0 mv0 mv  C R)
             (Build_VSE m0 mv0 mv' C R).

Definition VSEs_step (vses vses' : list VSE) : Prop :=
  Forall2 VSE_step vses vses'.

Inductive Last {A : Type} : A -> list A -> Prop :=
| LastSing : forall x, Last x [x]
| LastTail : forall x h t, Last x t -> Last x (h::t).

Lemma Last_unique {A : Type} (x x' : A) (l : list A) :
  Last x l -> Last x' l -> x = x'.
Proof.
  intro H; induction H; intro HLast; inversion HLast; subst; clear HLast; eauto;
    match goal with
    | [ H : Last _ [] |- _ ] => inversion H
    end.
Qed.

Lemma VSE_step_preserves_in :
  forall vse vses vses' mv' O,
  In vse vses ->
  Forall2 VSE_step vses vses' ->
  step (curr_variant vse) = (mv',O) ->
  In (upd_curr mv' vse) vses'.
Proof.
  intros vse vses vses' N' O' HIn HForall HStep.
  induction HForall.
  - inversion HIn.
  - inversion H; subst; eauto; clear H.
    inversion HIn; subst; eauto.
    + destruct H0 as [ Obs HObs ].
      simpl in *.
      rewrite HObs in HStep.
      inversion HStep; subst; clear HStep.
      left; auto.
    + right. apply IHHForall; auto.
Qed.

Lemma VSE_step_preserves_last :
  forall vse vses vses' N' O,
  Last vse vses ->
  Forall2 VSE_step vses vses' ->
  step (curr_variant vse) = (N',O) ->
  Last (upd_curr N' vse) vses'.
Proof.
  intros vse vses vses' N' O' HIn HForall HStep.
  induction HForall.
  - inversion HIn.
  - inversion H; subst; eauto; clear H.
    inversion HIn; subst; eauto.
    + destruct H0 as [ Obs HObs ].
      simpl in *.
      rewrite HObs in HStep.
      inversion HStep; subst; clear HStep.
      inversion HForall; subst; clear HForall.
      left; auto.
    + right. apply IHHForall; auto.
Qed.

Lemma Last_implies_In {A : Type} (x : A) (l : list A) :
  Last x l -> In x l.
Proof.
  intros Last; induction Last.
  - left; auto.
  - right; auto.
Qed.

Definition VarStack := list VSE.

(* Well-formedness conditions on the stack with respect to a current MS. *)
Definition WellFormedVS (M : MachineState) (vs : VarStack) : Prop :=
  (* The curr_variant field is a variant of the current state. *)
  Forall (fun vse => variantOf M (curr_variant vse) (contour vse)) vs /\
  (* The stack is nonempty and the last retP is const False *)
  (exists vse, Last vse vs /\ retP vse = fun _ => False) /\
  (* The current state is in the trace of *every* init machine. *)
  (Forall (fun vse => InTrace M (MTraceOf (init_machine vse))) vs) /\
  (* The variant state is in the trace of its own init variant. *)
  (Forall (fun vse => InTrace (curr_variant vse) (MTraceOf (init_variant vse))) vs).

CoInductive EagerStackSafetyTest (cm : CallMap) : MPTrace -> VarStack -> Prop :=
| EagerTestHalt :
    forall mp vs,
      WellFormedVS (ms mp) vs ->
      EagerStackSafetyTest cm (finished mp) vs
| EagerTestStep :
    forall mp MP vs vs' m' p' OM,
      (* Not a call or a return *)
      (forall args, ~ isCall cm (ms mp) args) ->
      (forall vse, In vse vs -> ~ (retP vse (ms mp))) ->
      (* Take a step. *)
      mpstep mp = Some (m', p', OM) ->
      WellFormedVS (ms mp) vs ->
      (* Enforce confidentiality for each variant. *)
      (forall vse,
          In vse vs ->
          exists mv' OV, step (curr_variant vse) = (mv', OV) /\
          EagerConfidentialityTest (retP vse) (ms mp) m' (curr_variant vse) mv' OM OV) ->
      (* Enforce integrity for main trace, but for each possible level in NCRs? *)
      (forall vse,
          In vse vs ->
          EagerIntegrityTest (contour vse) (ms mp) m') ->
      (* Step all variants and just recurse *)
      VSEs_step vs vs' ->
      head MP = (m',p') ->
      EagerStackSafetyTest cm MP vs' ->
      (* Conclude for current. *)
      EagerStackSafetyTest cm (notfinished mp MP) vs
| EagerTestCall :
    forall args mp MP vs vs' m' p' OM C,      
      (* Is a call *)
      isCall cm (ms mp) args ->
      (* (forall N C R, In (N,C,R) NCRs -> ~ R M) -> *)
      (* Take a step. *)
      mpstep mp = Some (m', p', OM) ->
      WellFormedVS (ms mp) vs ->
      (* Enforce confidentiality for each variant. *)
      (forall vse,
          In vse vs ->
          exists mv' OV, step (curr_variant vse) = (mv', OV) /\
          EagerConfidentialityTest (retP vse) (ms mp) m' (curr_variant vse) mv' OM OV) ->
      (* Enforce integrity for main trace, but for each possible level in NCRs? *)
      (forall vse,
          In vse vs ->
          EagerIntegrityTest (contour vse) (ms mp) m') ->
      (* Step all variants. *)
      VSEs_step vs vs' ->
      head MP = (m', p') ->
      (* Calculate the new contour based on the top of the current machine. *)
      makeContour args (ms mp) = C ->
      (* Recurse with every variant at the new contour at the top. *)
      (forall mvar, variantOf (ms mp) mvar C ->
                    EagerStackSafetyTest cm MP
                                         ({| init_machine := ms mp
                                           ; init_variant := mvar
                                           ; curr_variant := mvar
                                           ; contour := C
                                           ; retP := isRet (ms mp)
                                          |} :: vs')) ->
      (* Conclude for current. *)
      EagerStackSafetyTest cm (notfinished mp MP) vs
| EagerTestRet :
    forall mp MP vs vs' m' p' OM,          
      (* Is a return *)
      (* isCall cm M args -> *)
      (exists vse, In vse vs /\ retP vse (ms mp)) ->
        (* (forall N C R, In (N,C,R) NCRs -> ~ R M) -> *)
      (* Take a step. *)
      mpstep mp = Some (m', p', OM) ->
      WellFormedVS (ms mp) vs ->
      (* Enforce confidentiality for each variant. *)
      (forall vse,
          In vse vs ->
          exists mv' OV, step (curr_variant vse) = (mv', OV) /\
          EagerConfidentialityTest (retP vse) (ms mp) m' (curr_variant vse) mv' OM OV) ->
      (* Enforce integrity for main trace, but for each possible level in NCRs? *)
      (forall vse,
          In vse vs ->
          EagerIntegrityTest (contour vse) (ms mp) m') ->
      (* Step all variants. *)
      VSEs_step vs vs' ->
      head MP = (m',p') ->
      (* Recurse but take of the top of the stack. *)
      EagerStackSafetyTest cm MP (tl vs') ->
      (* Conclude for current. *)
      EagerStackSafetyTest cm (notfinished mp MP) vs.

Definition EagerStackSafetyTest' cm C MP :=
  forall mv, variantOf (ms (head MP)) mv C ->
  EagerStackSafetyTest cm MP [Build_VSE (ms (head MP)) mv mv C (fun _ => False)].

Ltac in_reasoning :=
  repeat match goal with
         | [ H : In _ [] |- _ ] => inversion H
         | [ H : In _ [_] |- _ ] => inversion H; subst; clear H
         | [ H : (_,_,_,_) = (_,_,_,_) |- _ ] => inversion H; subst; clear H
         end.

Ltac progress_integrity :=
  repeat match goal with
         | [ H : WellFormedVS ?M ?VS |- _ ] =>
           destruct H as [HVar [[vse_last' [HLast' HRet]] [HMTrace HNTrace]]]
         | [ H1 : Last ?X ?L, H2 : Last ?Y ?L |- _ ] =>
           assert (Y = X) by (eapply Last_unique; eauto); subst; clear H2
         end.

Theorem TestImpliesIntegrityToplevel :
  forall cm C MM vs,
    (exists vse, Last vse vs /\ contour vse = C) ->
  EagerStackSafetyTest cm MM vs -> EagerStackIntegrity' C MM.
Proof.
  cofix COFIX.
  intros cm C MP vs [vse_last [HLast HC]] Safety.
  inversion Safety; subst.
  - apply SI_finished.
  - apply SI_notfinished; progress_integrity.
    + intros k Hk.
      unfold MPState, EagerIntegrityTest in *.
      rewrite H6; simpl.
      eauto using Last_implies_In.
    + apply (COFIX cm (contour vse_last) MP0 vs'); auto.
      unfold VSEs_step in *.
      destruct (H3 vse_last (Last_implies_In vse_last vs HLast))
        as [N' [ON [HN' HConf]]].
      exists (upd_curr N' vse_last); split; auto.
      eapply VSE_step_preserves_last; eauto.
  - apply SI_notfinished; progress_integrity.
    + intros k Hk.
      unfold MPState, EagerIntegrityTest in *.
      rewrite H5.
      eauto using Last_implies_In.
    + apply (COFIX cm (contour vse_last) MP0 ((Build_VSE (ms mp) (ms mp) (ms mp) (makeContour args (ms mp)) (isRet (ms mp)))::vs')).
      * unfold VSEs_step in *.
        destruct (H2 vse_last)
          as [N' [ON [HN' HConf]]]; eauto using Last_implies_In.
        exists (upd_curr N' vse_last); split; auto.
        right; eauto using VSE_step_preserves_last.
      * apply H7.
        unfold variantOf.
        auto.
  - apply SI_notfinished; progress_integrity.
    + intros k Hk.
      unfold MPState, EagerIntegrityTest in *.
      rewrite H5.
      eauto using Last_implies_In.
    + apply (COFIX cm (contour vse_last) MP0 (tl vs')); auto.
      unfold VSEs_step in *.
      destruct (H2 vse_last)
        as [N' [ON [HN' HConf]]]; eauto using Last_implies_In.
      destruct vs.
      * inversion H4; subst.
        inversion HLast.
      * simpl in *.
        destruct vs'; inversion H4; subst; clear H4; simpl in *.
        inversion HLast; subst; clear HLast; eauto using VSE_step_preserves_last.
        { destruct H as [vse [[? | Contra] Contra']].
          + subst.
            rewrite HRet in Contra'; exfalso; eauto.
          + inversion Contra.
        }
Qed.

(*
Theorem TestImpliesConfidentialityToplevel :
  forall cm C MM MNCRs,
  (exists M N, Last (M,N,C,fun _ => False) MNCRs) ->
  EagerStackSafetyTest cm MM MNCRs ->
  forall N, variantOf (head MM) N C ->
            StrongEagerStackConfidentiality (fun _ => False) MM (traceOf N).
Proof.

  cofix COFIX.
  intros cm C MM MNCRs [M0 [N0 HLast]] Safety N Var.
  inversion Safety; subst; clear Safety.
  - remember HLast as HIn; clear HeqHIn; apply Last_implies_In in HIn.
    simpl in *.
    specialize (H0 M0 C N (fun _ => False) HIn).
    rewrite (idTrace_eq (traceOf N)); simpl.
    rewrite
 *)

(* ********* SNA Beware : Lazy Properties ********* *)

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
Definition ObservableIntegrity (C:Contour) (MP:MPTrace) (MPsuffO:option MPTrace) : Prop :=
 match MPsuffO with
 | Some actual =>
   let ideal := MTraceOf (RollbackInt C (ms (head MP)) (ms (head actual))) in
   ObsTracePrefix (ObsTraceOfM ideal) (ObsTraceOf actual)
 | None => True
 end.

(* A confidentiality rollback aims to undo a variation, so it restores the values of the
   original, unvaried state. But if the varied values were overwritten after they were varied,
   the changes should be kept. Otherwise we are building in some integrity. *)
Definition RollbackConf (Mstart Nstart Nend : MachineState) : MachineState :=
  fun k => if weq (Nstart k) (Nend k) && negb (weq (Mstart k) (Nstart k))
           then Mstart k
           else Nend k.

Definition ObservableConfidentiality (C:Contour) (MP:MPTrace) (isRet:MachineState -> Prop) : Prop :=
  forall n N NO,
    variantOf (ms (head MP)) n C ->
    TraceSpan (fun n' => ~ isRet n') (MTraceOf n) N NO ->
    let variant := N ^ (option_map (fun N' => MTraceOf (RollbackConf (ms (head MP)) n (head N'))) NO) in
    ObsTracePrefix (ObsTraceOfM variant) (ObsTraceOf MP).

Definition LazyStackSafety (cm : CallMap) (MP:MPTrace) : Prop :=
  ObservableConfidentiality (makeContour 0 (ms (head MP))) MP (fun _ => False) /\
  (forall MP' MP'' C' MPsuffO,
    FindCall cm (mapTrace ms MP) C' (mapTrace ms MP') ->
    TraceSpan (fun mp => ~isRet (ms (head MP')) (ms mp)) MP' MP'' MPsuffO ->
    ObservableIntegrity C' MP'' MPsuffO /\
    ObservableConfidentiality C' MP' (isRet (ms (head MP')))).

(* More conjectural stuff follows. *)

(* This is meant to rollback in all of the cases that either an integrity or a confidentiality
   rollback would. If a component is HI, it should always be rolled back; if HC but LI, it
   should be rolled back only if it kept the value of its variant. *)
Definition RollbackCI (C: Contour) (Mstart Nstart Nend : MachineState) : MachineState :=
  RollbackInt C Mstart (RollbackConf Mstart Nstart Nend).

Definition ObservableConfidentegrity (C:Contour) (MP:MPTrace) (MPsuffO:option MPTrace) (isRet:MachineState -> Prop) :=
  forall n N NO,
    variantOf (ms (head MP)) n C ->
    TraceSpan (fun n' => ~ isRet n') (MTraceOf n) N NO ->
    let actual := MP ^ MPsuffO in
    let ideal := N ^ (option_map (fun N' => MTraceOf (RollbackCI C (ms (head MP)) n (head N'))) NO) in
    ObsTracePrefix (ObsTraceOfM ideal) (ObsTraceOf actual).

Definition RealMTrace (M:MTrace) : Prop :=
  M = MTraceOf (head M).

Definition RealMPTrace (MP:MPTrace) : Prop :=
  RealMTrace (mapTrace ms MP).

Definition LazyStackSafety' (cm : CallMap) (MP:MPTrace) : Prop :=
  ObservableConfidentegrity (makeContour 0 (ms (head MP))) MP None (fun _ => False) /\
  (forall MP' MP'' C' MPsuffO, FindCall cm (mapTrace ms MP) C' (mapTrace ms MP') ->
                          TraceSpan (fun mp => ~isRet (ms (head MP')) (ms mp)) MP' MP'' MPsuffO ->
                          ObservableConfidentegrity C' MP'' MPsuffO (isRet (ms (head MP'')))).

Axiom SpanEndsIfSuffix :
  forall A (f : A -> Prop) (MM MM' MM'' : Trace A) (MMO : option (Trace A)),
    TraceSpan f MM MM' MMO ->
    MMO = Some MM'' ->
    exists M, IsEnd MM' M.

Axiom SpanSuffixIsReal :
  forall f MM MM' MMsuff,
    RealTrace MM ->
    TraceSpan f MM MM' (Some MMsuff) ->
    RealTrace MMsuff.
    
Axiom StepOverSpan :
  forall f (MM MM' MMsuff : MTrace) M,
  RealTrace MM ->
  TraceSpan f MM MM' (Some MMsuff) ->
  IsEnd MM' M ->
  exists O, step M = Some (head MMsuff,O).

Lemma FHoldsOnSpanContents :
  forall A (f:A->Prop) MM MM' MMO,
    TraceSpan f MM MM' MMO ->
    ForallTrace f MM'.
Proof.
  intros. destruct H. destruct H0. auto.
Qed.
  
Lemma IsEndInTrace :
  forall A (M:A) (MM:Trace A),
    IsEnd MM M -> InTrace M MM.
Proof.
  intros. induction H.
  - constructor.
  - constructor. auto.
Qed.

Lemma ForallInTrace :
  forall A (f:A->Prop) MM M,
    InTrace M MM ->
    ForallTrace f MM ->
    f M.
Proof.
  intros. induction H; inversion H0; auto.
Qed.
  
Axiom ObsTraceEq_refl :
  forall OO,
    ObsTraceEq OO OO.

Lemma EagerImpliesLazyInt :
  forall f C args MM MM' MMO,
    RealTrace MM ->
    C = makeContour args (head MM) ->
    TraceSpan f MM MM' MMO ->
    (forall M M' a O, f M -> step M = Some (M',O) -> M' (Mem a) = M (Mem a)) ->
    EagerStackIntegrity C MM' -> ObservableIntegrity C MM' MMO.
Proof.
  unfold EagerStackIntegrity. unfold ObservableIntegrity. intros.
  destruct MMO as [MMsuff |] eqn:E; auto. rewrite <- E in H1.
  apply (SpanEndsIfSuffix MachineState f MM MM' MMsuff MMO) in H1 as HEnd; auto. destruct HEnd as [M].
  assert (forall k, integrityOf (C k) = HI -> (head MM') k = M k).
  { intros; destruct k; simpl.
    - apply H3; try apply IsEndInTrace; auto.
    - rewrite H0 in H5. simpl in H5. discriminate. }
  assert (exists O, step M = Some (head MMsuff,O)).
  { apply (StepOverSpan f MM MM');auto. rewrite E in H1. auto. }
  destruct H6 as [O H6].
  assert (forall k, integrityOf (C k) = HI -> (head MMsuff) k = M k).
  { intros; destruct k; simpl.
    - apply (H2 M (head MMsuff) a O);auto.
      apply (ForallInTrace MachineState f MM' M).
      + apply IsEndInTrace;auto.
      + apply (FHoldsOnSpanContents MachineState f MM MM' MMO); auto.
    - rewrite H0 in H7. simpl in H7. discriminate. }
  assert (RollbackInt C (head MM') (head MMsuff) = head MMsuff).
  { unfold RollbackInt. extensionality k. destruct (integrityOf (C k)) eqn:E2.
    + apply (H7 k) in E2 as Hright. apply (H5 k) in E2 as Hleft.
      rewrite Hright. rewrite Hleft. auto.
    + auto. }
  rewrite H8. apply (SpanSuffixIsReal f MM MM' MMsuff) in H; try rewrite <- E; auto.
  unfold RealTrace in H. rewrite <- H. apply ObsTraceEq_refl.
Qed.
  
Lemma EagerImpliesLazyConf :
  forall C MM MMO isRet,
    EagerStackConfidentiality C MM isRet -> ObservableConfidentiality C (MM^MMO) isRet.
Proof.
  unfold EagerStackConfidentiality. unfold ObservableConfidentiality. intros.
  apply (H N NN Mret) in H0.
  - destruct H0. 
  - 
                                                          
Theorem EagerSafetyImpliesLazy :
  forall cm C MM,
    EagerStackSafety cm MM C -> LazyStackSafety cm C MM.
Proof.
  intros. unfold EagerStackSafety in H. unfold LazyStackSafety. split.
  - 
  -

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
