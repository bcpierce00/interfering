From StackSafety Require Import Trace MachineModule.

Module ObsTrace (M:Machine).
  Import M.

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

  Ltac join_frobber :=
    repeat match goal with
           | |- context[(finished ?T) ^^ ?OT] =>
             rewrite (idTrace_eq (finished T ^^ OT)); simpl
           | |- context[(notfinished ?O ?T) ^^ ?OT] =>
             rewrite (idTrace_eq (notfinished O T ^^ OT)); simpl
           | [H: context[(finished ?T) ^^ ?OT] |- _ ] =>
             rewrite (idTrace_eq (finished T ^^ OT)) in H; simpl in H
           | [H: context[(notfinished ?O ?T) ^^ ?OT] |- _ ] =>
             rewrite (idTrace_eq (notfinished O T ^^ OT)) in H; simpl in H
           end.

  Ltac maptrace_frobber :=
    repeat match goal with
           | |- context[mapTrace ?f (finished ?t)] =>
             rewrite (idTrace_eq (mapTrace f (finished t))); unfold mapTrace; simpl
           | |- context[mapTrace ?f (notfinished ?t ?T)] =>
             rewrite (idTrace_eq (mapTrace f (notfinished t T))); unfold mapTrace; simpl
           end.

  (********************** ObsTrace Equivalence *************************)

  CoInductive ObsTraceEq : TraceOf Observation -> TraceOf Observation -> Prop :=
  | ObsEqTau1 : forall OO OO'
                       (HR : ObsTraceEq OO OO' : Prop),
      ObsTraceEq (notfinished Tau OO) OO'
  | ObsEqTau2 : forall OO OO'
                       (HR : ObsTraceEq OO OO' : Prop),
      ObsTraceEq OO (notfinished Tau OO')
  | ObsEqNow : forall o OO OO'
                      (HR : ObsTraceEq OO OO' : Prop),
      ObsTraceEq (notfinished (Out o) OO) (notfinished (Out o) OO')
  (* The last thing we need is a way of handling *all-tau* traces.
     There are a couple of ways of doing that, not sure what will
   play better in proofs. *)
  | ObsEqAllSame : forall OO,
      ObsTraceEq(*_gen R*) OO OO.

  Hint Constructors ObsTraceEq : core.

  Notation "OO' ~=_O OO" := (ObsTraceEq OO' OO) (at level 80).

  Lemma ObsTraceEq_sym :
    forall O O',
      ObsTraceEq O O' -> ObsTraceEq O' O.
  Proof.
    cofix COFIX.
    intros O O' H.
    inv H;
      try (constructor; (apply COFIX; auto) || (auto)).
  Qed.

  Lemma ObsTraceEqRemoveTau1 :
    forall T T', ObsTraceEq (notfinished Tau T) T' -> ObsTraceEq T T'.
  Proof.
    cofix COFIX.
    intros T T' Eq.
    inv Eq.
    + assumption.
    + eapply ObsEqTau2.
      eapply COFIX; auto.
    + eapply ObsEqTau2.
      eapply ObsEqAllSame.
  Qed.

  Lemma ObsTraceEqRemoveTau2 :
    forall T T', ObsTraceEq T (notfinished Tau T') -> ObsTraceEq T T'.
  Proof.
    cofix COFIX.
    intros T T' Eq.
    inv Eq.
    + eapply ObsEqTau1.
      eapply COFIX.
      auto.
    + assumption.
    + eapply ObsEqTau1.
      eapply ObsEqAllSame.
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
      inversion Eq.
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
        intros Eq1 O2' O2 Eq2.
      + inversion Eq1; subst; simpl in *; clear Eq1; app_frobber.
        * destruct a.
          -- apply ObsEqNow; auto.
          -- apply ObsEqTau1. apply ObsEqTau2; auto.
      + inversion Eq1; subst; simpl in *; clear Eq1.
        specialize (IHLast' HR O2' O2 Eq2).
        app_frobber.
        eapply ObsEqTau2.
        auto.
    - destruct a'.
      + destruct (EqOut_tauN O1' o1' Last' e T Eq1) as [n [HTau | [T' HTau]]].
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
                eapply IHLast; eauto.
             ++ inversion Last'; subst; clear Last'.
                eapply IHLast; eauto.
          -- inversion Last'; subst; clear Last'.
             specialize (IHn H3).
             apply ObsTraceEqRemoveTau2 in Eq1.
             specialize (IHn Eq1).
             apply ObsEqTau2.
             auto.
      + apply ObsTraceEqRemoveTau1 in Eq1.
        app_frobber.
        apply ObsEqTau1.
        eapply IHLast; eauto.
  Qed.

(********************** ObsTrace Prefix *************************)

  (* The second is a prefix of the first, up to Tau *)
  CoInductive ObsTracePrefix : TraceOf Observation -> TraceOf Observation -> Prop :=
  | ObsPreTau1 : forall OO OO'
                        (HR : ObsTracePrefix OO OO' : Prop),
      ObsTracePrefix (notfinished Tau OO) OO'
  | ObsPreTau2 : forall OO OO'
                        (HR : ObsTracePrefix OO OO' : Prop),
      ObsTracePrefix OO (notfinished Tau OO')
  | ObsPreNow : forall w OO OO'
                       (HR : ObsTracePrefix OO OO' : Prop),
      ObsTracePrefix (notfinished (Out w) OO) (notfinished (Out w) OO')
  | ObsPreFinishedOut2 : forall w OO,
      ObsTracePrefix (notfinished (Out w) OO) (finished (Out w))
  | ObsPreFinishedTau : forall OO,
      ObsTracePrefix OO (finished Tau)
  | ObsPreAllSame : forall OO,
      ObsTracePrefix OO OO.
  Hint Constructors ObsTracePrefix : core.

  Notation "OO' <=_O OO" := (ObsTracePrefix OO OO') (at level 80).

  Lemma ObsTracePrefix_refl : forall OO, ObsTracePrefix OO OO.
  Proof.
    cofix CH.
    intros [o | o OO](*; pfold*).
    - constructor. 
    - destruct o as [w |].
      + apply ObsPreNow. now auto.
      + apply ObsPreTau1. (*left. pfold.*) apply ObsPreTau2. now auto.
  Qed.

  Lemma ObsTracePrefRemoveTau1 :
    forall T T', (notfinished Tau T) <=_O T' -> T <=_O T'.
  Proof.
    cofix COFIX.
    intros T T' Pref.
    inv Pref.
    + constructor. apply COFIX. auto.
    + assumption.
    + constructor.
      apply ObsTracePrefix_refl.
  Qed.
  
  Lemma ObsTracePrefRemoveTau2 :
    forall T T', T <=_O (notfinished Tau T') -> T <=_O T'.
  Proof.
    cofix COFIX.
    intros T T' Pref.
    inv Pref.
    + assumption.
    + constructor. apply COFIX. auto.
    + constructor. 
    + constructor. 
      apply ObsTracePrefix_refl.
  Qed.

  Lemma ObsTracePrefFinished: forall OO, OO <=_O finished Tau -> OO ~=_O finished Tau.
  Proof.
    cofix COFIX. 
    intros. 
    inv H.
    - constructor. apply COFIX; auto.
    - constructor. 
    - constructor. 
  Qed.

  (********************** Relationship betweeen Traces and ObsTraces  *************************)


  Lemma TraceEqImpliesObsTraceEq :
    forall O O',
      O ~= O' ->
      ObsTraceEq O O'.
  Proof.
    cofix COFIX. intros O O' H. inv H.
    - constructor.
    - destruct a.
      + constructor. auto.
      + constructor. constructor. auto.
  Qed.

  Lemma ObsTraceEqImpliesPrefix :
    forall O O',
      ObsTraceEq O O' ->
      O <=_O O'.
  Proof.
    cofix COFIX. intros O O' H.
    inv H; constructor; apply COFIX; auto.
  Qed.

  Lemma ObsPrefOverEq :
    forall O1 O1' O2,
      O1 ~= O1' ->
      O1 <=_O O2 ->
      O1' <=_O O2.
  Proof.
    cofix COFIX. intros O1 O1' O2 H H0. inv H.
    - assumption.
    - destruct a.
      + inv H0.
        * constructor.
          apply (COFIX (notfinished (Out e) T1) (notfinished (Out e) T2) OO).
          -- constructor. auto.
          -- auto.
        * constructor. apply (COFIX T1 T2 OO); auto.
        * constructor.
          apply ObsTraceEqImpliesPrefix. apply TraceEqImpliesObsTraceEq in H1.
          apply ObsTraceEq_sym. auto.
      + constructor. (*right.*) apply (COFIX T1 T2 O2); auto. apply ObsTracePrefRemoveTau1. auto.
  Qed.

  Lemma ObsPrefOverEq2 :
    forall O1 O2 O2',
      O2 ~= O2' ->
      O1 <=_O O2 ->
      O1 <=_O O2'.
  Proof.
    cofix COFIX. intros O1 O2 O2' H H0. inv H.
    - assumption.
    - destruct a.
      + inv H0.
        * constructor.
          apply (COFIX OO' (notfinished (Out e) T1) (notfinished (Out e) T2)).
          -- constructor. auto.
          -- auto.
        * constructor. apply (COFIX OO' T1 T2); auto.
        * constructor.
        * constructor.
        * constructor. apply ObsTraceEqImpliesPrefix. apply TraceEqImpliesObsTraceEq. auto.
      + constructor. apply (COFIX O1 T1 T2); auto. apply ObsTracePrefRemoveTau2. auto.
  Qed.

  Lemma ObsEqOverEq :
    forall O1 O1' O2,
      O1 ~= O1' ->
      ObsTraceEq O1 O2 ->
      ObsTraceEq O1' O2.
  Proof.
    cofix COFIX. intros O1 O1' O2 H H0(*; pfold*). inv H.
    - assumption.
    - destruct a.
      + inv H0.
        * constructor.
          apply (COFIX (notfinished (Out e) T1) (notfinished (Out e) T2) OO').
          -- constructor. auto.
          -- auto.
        * constructor. apply (COFIX T1 T2 OO'); auto.
        * constructor.
          apply ObsTraceEq_sym. apply TraceEqImpliesObsTraceEq. auto.
      + constructor. apply (COFIX T1 T2 O2); auto. apply ObsTraceEqRemoveTau1. auto.
  Qed.

End ObsTrace.
