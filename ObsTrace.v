Require Import Trace.

Variable Word:Type.

(* Observations are values, or silent (tau) *)
Inductive Observation :=
| Out (w : Word)
| Tau.

Definition ObsTrace := TraceOf Observation.

Ltac app_frobber :=
  repeat match goal with
         | |- context[(finished ?T) ^ ?OT] =>
           rewrite (idTrace_eq (finished T ^ OT)); simpl
         | |- context[(notfinished ?O ?T) ^ ?OT] =>
           rewrite (idTrace_eq (notfinished O T ^ OT)); simpl
         | [H: context[(finished ?T) ^ ?OT] |- _ ] =>
           rewrite (idTrace_eq (finished T ^ OT)) in H; simpl in H
         | [H: context[(notfinished ?O ?T) ^ ?OT] |- _ ] =>
           rewrite (idTrace_eq (notfinished O T ^ OT)) in H; simpl in H
         end.

(********************** ObsTrace Equivalence *************************)

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

Lemma ObsTraceEq_sym :
  forall O O',
    ObsTraceEq O O' -> ObsTraceEq O' O.
Proof.
  cofix COFIX. 
  intros.
  inversion H; subst; clear H;
    try (constructor; apply COFIX; auto). 
Qed.

Lemma ObsTraceEqRemoveTau1 :
  forall T T', ObsTraceEq (notfinished Tau T) T' -> ObsTraceEq T T'.
Proof.
  cofix COFIX.
  intros T T' Eq.
  inversion Eq; subst; clear Eq.
  + auto.
  + eapply ObsEqTau2.
    eapply COFIX; auto.
  + eapply ObsEqTau2.
    eapply ObsEqAllTau.
Qed.

Lemma ObsTraceEqRemoveTau2 :
  forall T T', ObsTraceEq T (notfinished Tau T') -> ObsTraceEq T T'.
Proof.
  cofix COFIX.
  intros T T' Eq.
  inversion Eq; subst; clear Eq.
  + eapply ObsEqTau1.
    eapply COFIX.
    auto.
  + auto. 
  + eapply ObsEqTau1.
    eapply ObsEqAllTau.
Qed.

Fixpoint tauN (n : nat) (T : TraceOf Observation) : TraceOf Observation :=
  match n with
  | O => T
  | S n' => notfinished Tau (tauN n' T)
  end.

Lemma EqOut_tauN : forall T' t',
    Last T' t' ->
    forall w T, 
      ObsTraceEq (notfinished (Out w) T) T' ->
      exists n, T' = tauN n (finished (Out w)) \/ exists  T'', T' = tauN n (notfinished (Out w) T'').
Proof.
  intros T' t' HL.
  induction HL; intros w Tw Eq.
  - exists 0. left. simpl.
    inversion Eq.
  - destruct a'.
    + inversion Eq; subst; clear Eq.
      * exists 0.
        right.
        exists T; simpl; auto.
      * exists 0.
        right.
        exists T; simpl; auto.
    + inversion Eq; subst; clear Eq.
      destruct (IHHL w Tw H1) as [n [HTau | [T'' HTau]]].
      * exists (S n).
        left.
        simpl.
        rewrite HTau.
        auto.
      * exists (S n).
        right.
        simpl.
        exists T''.
        rewrite HTau.
        auto.
Qed.

Lemma ObsTraceEqApp :
  forall O1 O1' O2 O2' o1 o1',
    Last O1 o1 -> Last O1' o1' -> 
    ObsTraceEq O1 O1' ->
    ObsTraceEq O2 O2' ->
    ObsTraceEq (O1^(Some O2)) (O1'^(Some O2')).
Proof.
    intros O1 O1' O2 O2' o1 o1' H;
    revert O1' O2 O2' o1'.
  induction H as [o1|]; intros O1' O2 O2' o1' Last' Eq1 Eq2.
  - generalize dependent O2;
    generalize dependent O2';
    generalize dependent Eq1.
    induction Last';
      intros Eq1 O2' O2 Eq2.
    + inversion Eq1; subst; simpl in *; clear Eq1; app_frobber.
      * apply ObsEqNow; auto.
      * apply ObsEqTau1; apply ObsEqTau2; auto.
      * destruct a.
        -- apply ObsEqNow; auto.
        -- apply ObsEqTau1; apply ObsEqTau2; auto.
    + inversion Eq1; subst; simpl in *; clear Eq1.
      specialize (IHLast' H1 O2' O2 Eq2).      
      app_frobber.
      eapply ObsEqTau2.
      auto.
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq1) as [n [HTau | [T' HTau]]].
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsEqNow.
           inversion Eq1.
        -- apply ObsEqTau2.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn H3 Eq1).
           auto.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsEqNow.
           inversion Eq1; subst; clear Eq1.
           ++ inversion Last'; subst; clear Last'.
              eauto.
           ++ inversion Last'; subst; clear Last'.
              eauto using ObsEqAllTau.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn Eq1).
           apply ObsEqTau2.
           auto.
    + apply ObsTraceEqRemoveTau1 in Eq1.
      app_frobber.
      apply ObsEqTau1.
      eauto.
Qed.

(********************** ObsTrace Prefix *************************)

(* The second is a prefix of the first, up to Tau *)
CoInductive ObsTracePrefix : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsPreTau1 : forall OO OO',
    ObsTracePrefix OO OO' ->
    ObsTracePrefix (notfinished Tau OO) OO'
| ObsPreTau2 : forall OO OO',
    ObsTracePrefix OO OO' ->
    ObsTracePrefix OO (notfinished Tau OO')
| ObsPreNow : forall w OO OO',
    ObsTracePrefix OO OO' ->
    ObsTracePrefix (notfinished (Out w) OO) (notfinished (Out w) OO')
| ObsPreFinishedOut1 : forall w,
    ObsTracePrefix (finished (Out w)) (finished (Out w))
| ObsPreFinishedOut2 : forall w OO,
    ObsTracePrefix (notfinished (Out w) OO) (finished (Out w))
| ObsPreFinishedTau : forall OO,
    ObsTracePrefix OO (finished Tau)
| ObsPreAllTau : forall OO,
     ObsTracePrefix OO OO.

Notation "OO' <=_O OO" := (ObsTracePrefix OO OO') (at level 80).

Definition ObsTracePrefApp' :
  forall O1 O1' O2 O2' o1 o1',
    Last O1 o1 -> Last O1' o1' -> 
    ObsTraceEq O1 O1' ->
    ObsTracePrefix O2 O2' ->
    ObsTracePrefix (O1^(Some O2)) (O1'^(Some O2')).
Proof.
  intros O1 O1' O2 O2' o1 o1' H;
    (* I really want SSR... *)
    revert O1' O2 O2' o1'.
  induction H as [o1|]; intros O1' O2 O2' o1' Last' Eq Pref.
  - generalize dependent O2;
    generalize dependent O2';
    generalize dependent Eq.
    induction Last';
      intros Eq O2' O2 Pref.
    + inversion Eq; subst; simpl in *; clear Eq; app_frobber.
      (* Hint constructors doesn't work for this? *)
      * apply ObsPreNow; auto.
      * apply ObsPreTau1; apply ObsPreTau2; auto.
      * destruct a.
        -- apply ObsPreNow; auto.
        -- apply ObsPreTau1; apply ObsPreTau2; auto.
    + inversion Eq; subst; simpl in *; clear Eq.
      specialize (IHLast' H1 O2' O2 Pref).      
      app_frobber.
      eapply ObsPreTau2.
      auto.
  (* Try by inversion. *)
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq) as [n [HTau | [T' HTau]]].
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsPreNow.
           inversion Eq. (* This makes me feel strange *)
        -- apply ObsPreTau2.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn H3 Eq).
           auto.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsPreNow.
           inversion Eq; subst; clear Eq.
           ++ inversion Last'; subst; clear Last'.
              eauto.
           ++ inversion Last'; subst; clear Last'.
              eauto using ObsEqAllTau.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn Eq).
           apply ObsPreTau2.
           auto.
    + apply ObsTraceEqRemoveTau1 in Eq.
      app_frobber.
      apply ObsPreTau1.
      eauto.
Qed.
