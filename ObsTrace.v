Require Import Trace.
Require Import Machine.
Require Import Paco.paco.

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

Inductive ObsTraceEq_gen R : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsEqTau1 : forall OO OO'
                     (HR : R OO OO' : Prop),
    ObsTraceEq_gen R (notfinished Tau OO) OO'
| ObsEqTau2 : forall OO OO'
                     (HR : R OO OO' : Prop),
    ObsTraceEq_gen R OO (notfinished Tau OO')
| ObsEqNow : forall w OO OO'
                     (HR : R OO OO' : Prop),
    ObsTraceEq_gen R (notfinished (Out w) OO) (notfinished (Out w) OO')
| ObsEqFinishedOut : forall w,
    ObsTraceEq_gen R (finished (Out w)) (finished (Out w))
| ObsEqFinishedTau :
    ObsTraceEq_gen R (finished Tau) (finished Tau)
(* The last thing we need is a way of handling *all-tau* traces.
   There are a couple of ways of doing that, not sure what will
   play better in proofs. *)
| ObsEqAllTau : forall OO,
     ObsTraceEq_gen R OO OO.
(* APT: Establishing equality between traces seems hard, and this overlaps
the previous two cases.  Maybe try:
   ForallTrace (fun o => o = Tau) OO ->
   ForallTrace (fun o => o = Tau) OO' ->
   ObsTraceEq OO OO'
?
LEO: That was the other thing I had in mind. I'll see what makes proofs easier.
(Note that this proposal overlaps with the first two cases, as well as the last one.)
 *)
Hint Constructors ObsTraceEq_gen : core.

Definition ObsTraceEq (OO OO' : TraceOf Observation) :=
  paco2 ObsTraceEq_gen bot2 OO OO'.
Hint Unfold ObsTraceEq : core.
Lemma ObsTraceEq_mon : monotone2 ObsTraceEq_gen. Proof. pmonauto. Qed.
Hint Resolve ObsTraceEq_mon : paco.

Notation "OO' ~=_O OO" := (ObsTraceEq OO' OO) (at level 80).

Lemma ObsTraceEq_sym :
  forall O O',
    ObsTraceEq O O' -> ObsTraceEq O' O.
Proof.
  pcofix COFIX.
  intros O O' H; pfold.
  inv H;
    try (constructor; (right; apply COFIX; auto) || (left; auto)).
Qed.

Lemma ObsTraceEqRemoveTau1 :
  forall T T', ObsTraceEq (notfinished Tau T) T' -> ObsTraceEq T T'.
Proof.
  pcofix COFIX.
  intros T T' Eq; pfold.
  inv Eq.
  + (* RB: This goal is slightly more involved than it was before. *)
    apply paco2_unfold.
    * apply ObsTraceEq_mon.
    * apply paco2_mon_bot with ObsTraceEq_gen; auto.
  + eapply ObsEqTau2.
    right. eapply COFIX; auto.
  + eapply ObsEqTau2.
    left. pfold. eapply ObsEqAllTau.
Qed.

Lemma ObsTraceEqRemoveTau2 :
  forall T T', ObsTraceEq T (notfinished Tau T') -> ObsTraceEq T T'.
Proof.
  pcofix COFIX.
  intros T T' Eq; pfold.
  inv Eq.
  + eapply ObsEqTau1.
    right. eapply COFIX.
    auto.
  + (* RB: This goal is slightly more involved than it was before. *)
    apply paco2_unfold.
    * apply ObsTraceEq_mon.
    * apply paco2_mon_bot with ObsTraceEq_gen; auto.
  + eapply ObsEqTau1. left. pfold.
    eapply ObsEqAllTau.
Qed.

Fixpoint tauN (n : nat) (T : ObsTrace) : ObsTrace := 
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
    pinversion Eq.
  - destruct a'.
    + inv Eq.
      * exists 0.
        right.
        exists T; simpl; auto.
      * exists 0.
        right.
        exists T; simpl; auto.
    + inv Eq.
      destruct (IHHL w Tw HR) as [n [HTau | [T'' HTau]]].
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
      intros Eq1 O2' O2 Eq2;
      pfold.
    + pinversion Eq1; subst; simpl in *; clear Eq1; app_frobber.
      * apply ObsEqNow; auto.
      * apply ObsEqTau1. left. pfold. apply ObsEqTau2; auto.
      * destruct a.
        -- apply ObsEqNow; auto.
        -- apply ObsEqTau1. left. pfold. apply ObsEqTau2; auto.
    + pinversion Eq1; subst; simpl in *; clear Eq1.
      specialize (IHLast' HR O2' O2 Eq2).
      app_frobber.
      eapply ObsEqTau2.
      auto.
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq1) as [n [HTau | [T' HTau]]].
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber; pfold.
        -- apply ObsEqNow.
           pinversion Eq1.
        -- apply ObsEqTau2.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn H3 Eq1).
           auto.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber; pfold.
        -- apply ObsEqNow.
           pinversion Eq1; subst; clear Eq1.
           (* RB: The following two subgoals become slightly different. *)
           ++ inversion Last'; subst; clear Last'.
              left.
              eapply IHLast; eauto.
           ++ inversion Last'; subst; clear Last'.
              left.
              eapply IHLast; eauto.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn Eq1).
           apply ObsEqTau2.
           auto.
    + apply ObsTraceEqRemoveTau1 in Eq1.
      app_frobber.
      (* RB: Ditto here, applying IH is now a bit more explicit. *)
      pfold. apply ObsEqTau1. left.
      eapply IHLast; eauto.
Qed.

(********************** ObsTrace Prefix *************************)

(* LEO: I didn't like the non-coinductive nature of this... 
Definition ObsTracePrefix (OO OO' : TraceOf Observation) : Prop :=
  exists OO'', ObsTraceEq OO OO'' /\ OO' <<== OO'' \/ ObsTraceEq OO' OO'' /\ OO' <<== OO.
 *)

(* The second is a prefix of the first, up to Tau *)
Inductive ObsTracePrefix_gen R : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsPreTau1 : forall OO OO'
                      (HR : R OO OO' : Prop),
    ObsTracePrefix_gen R (notfinished Tau OO) OO'
| ObsPreTau2 : forall OO OO'
                      (HR : R OO OO' : Prop),
    ObsTracePrefix_gen R OO (notfinished Tau OO')
| ObsPreNow : forall w OO OO'
                      (HR : R OO OO' : Prop),
    ObsTracePrefix_gen R (notfinished (Out w) OO) (notfinished (Out w) OO')
| ObsPreFinishedOut1 : forall w,
    ObsTracePrefix_gen R (finished (Out w)) (finished (Out w))
| ObsPreFinishedOut2 : forall w OO,
    ObsTracePrefix_gen R (notfinished (Out w) OO) (finished (Out w))
| ObsPreFinishedTau : forall OO,
    ObsTracePrefix_gen R OO (finished Tau)
| ObsPreAllTau : forall OO,
     ObsTracePrefix_gen R OO OO.
Hint Constructors ObsTracePrefix_gen : core.

Definition ObsTracePrefix (OO OO' : TraceOf Observation) :=
  paco2 ObsTracePrefix_gen bot2 OO OO'.
Hint Unfold ObsTracePrefix : core.
Lemma ObsTracePrefix_mon : monotone2 ObsTracePrefix_gen. Proof. pmonauto. Qed.
Hint Resolve ObsTracePrefix_mon : paco.

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
      intros Eq O2' O2 Pref; pfold.
    + pinversion Eq; subst; simpl in *; clear Eq; app_frobber.
      (* Hint constructors doesn't work for this? *)
      * apply ObsPreNow; auto.
      * apply ObsPreTau1. left. pfold. apply ObsPreTau2; auto.
      * destruct a.
        -- apply ObsPreNow; auto.
        -- apply ObsPreTau1. left. pfold. apply ObsPreTau2; auto.
    + pinversion Eq; subst; simpl in *; clear Eq.
      specialize (IHLast' HR O2' O2 Pref).
      app_frobber.
      eapply ObsPreTau2.
      auto.
  (* Try by inversion. *)
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq) as [n [HTau | [T' HTau]]];
        pfold.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsPreNow.
           pinversion Eq. (* This makes me feel strange *)
        -- apply ObsPreTau2.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn H3 Eq).
           auto.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsPreNow.
           pinversion Eq; subst; clear Eq.
           (* RB: The following two subgoals become slightly different. *)
           ++ inversion Last'; subst; clear Last'.
              left.
              eapply IHLast; eauto.
           ++ inversion Last'; subst; clear Last'.
              left.
              eapply IHLast; eauto.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn Eq).
           apply ObsPreTau2.
           auto.
    + apply ObsTraceEqRemoveTau1 in Eq.
      app_frobber.
      pfold. apply ObsPreTau1. left.
      (* RB: Ditto here, applying IH is now a bit more explicit. *)
      eapply IHLast; eauto.
Qed.

Lemma ObsTracePrefix_refl : forall OO, ObsTracePrefix OO OO.
Proof.
  pcofix CH.
  intros [o | o OO]; pfold.
  - destruct o as [w |].
    + now apply ObsPreFinishedOut1.
    + now apply ObsPreFinishedTau.
  - destruct o as [w |].
    + apply ObsPreNow. now auto.
    + apply ObsPreTau1. left. pfold. apply ObsPreTau2. now auto.
Qed.


(********************** Relationship betweeen Traces and ObsTraces  *************************)


Lemma TraceEqImpliesObsTraceEq :
  forall O O',
    O ~= O' ->
    ObsTraceEq O O'.
Proof.
  pcofix COFIX. intros O O' H; pfold. inv H.
  - constructor.
  - destruct a.
    + constructor. auto.
    + constructor. left. pfold. constructor. auto.
Qed.

Lemma ObsTraceEqImpliesPrefix :
  forall O O',
    ObsTraceEq O O' ->
    O <=_O O'.
Proof.
  pcofix COFIX. intros O O' H. pfold.
  inv H; constructor; right; apply COFIX; auto.
Qed.

Lemma ObsTracePrefRemoveTau1 :
  forall T T', (notfinished Tau T) <=_O T' -> T <=_O T'.
Proof.
  pcofix COFIX.
  intros T T' Pref; pfold.
  inv Pref.
  + constructor. right. apply COFIX. auto.
  + (* RB: Some base cases like this need a little more work than before. *)
    apply paco2_unfold.
    * auto with paco.
    * eapply paco2_mon_bot; eauto with paco.
  + constructor. left.
    eapply paco2_mon_bot with ObsTracePrefix_gen; [| auto].
    apply ObsTracePrefix_refl.
Qed.

Lemma ObsPrefOverEq :
  forall O1 O1' O2,
    O1 ~= O1' ->
    O1 <=_O O2 ->
    O1' <=_O O2.
Proof.
  pcofix COFIX. intros O1 O1' O2 H H0; pfold. inv H.
  - apply paco2_unfold.
    + auto with paco.
    + eapply paco2_mon_bot; eauto with paco.
  - destruct a.
    + inv H0.
      * constructor. right.
        apply (COFIX (notfinished (Out w) T1) (notfinished (Out w) T2) OO).
        -- pfold. constructor. auto.
        -- auto.
      * constructor. right. apply (COFIX T1 T2 OO); auto.
      * constructor. left.
        apply paco2_mon_bot with ObsTracePrefix_gen; [| auto].
        apply ObsTraceEqImpliesPrefix. apply TraceEqImpliesObsTraceEq in H1.
        apply ObsTraceEq_sym. auto.
    + constructor. right. apply (COFIX T1 T2 O2); auto. apply ObsTracePrefRemoveTau1. auto.
Qed.

Lemma ObsEqOverEq :
  forall O1 O1' O2,
    O1 ~= O1' ->
    ObsTraceEq O1 O2 ->
    ObsTraceEq O1' O2.
Proof.
  pcofix COFIX. intros O1 O1' O2 H H0; pfold. inv H.
  - apply paco2_unfold.
    * auto with paco.
    * eapply paco2_mon_bot; eauto with paco.
  - destruct a.
    + inv H0.
      * constructor. right.
        apply (COFIX (notfinished (Out w) T1) (notfinished (Out w) T2) OO').
        -- pfold. constructor. auto.
        -- auto.
      * constructor. right. apply (COFIX T1 T2 OO'); auto.
      * constructor. left.
        apply paco2_mon_bot with ObsTraceEq_gen; [| auto].
        apply ObsTraceEq_sym. apply TraceEqImpliesObsTraceEq. auto.
    + constructor. right. apply (COFIX T1 T2 O2); auto. apply ObsTraceEqRemoveTau1. auto.
Qed.
