(* Investigating alternative definitions of ObsTraceEq in hopes of
 recovering transitivity. *)

Require Import Trace.
Require Import Machine.
(*Require Import Paco.paco.*)

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

Definition AllTau (T: ObsTrace) := 
   ForallTrace (fun o => o = Tau) T.

CoInductive InfTau : ObsTrace -> Prop :=
| inftau_intro: forall T, InfTau T -> InfTau (notfinished Tau T).

CoFixpoint inftau : ObsTrace := notfinished Tau inftau.

Lemma inftauis: InfTau inftau.
cofix COFIX.
rewrite idTrace_eq. simpl. constructor. apply COFIX. 
Qed.

Lemma inftauonly: forall T, InfTau T -> T ~= inftau.
cofix COFIX.
intros.
inv H. 
rewrite (idTrace_eq inftau).  simpl.  constructor.  apply COFIX. 
auto.
Qed.

Lemma inftaueq : forall T1 T2,  InfTau T1 -> T1 ~= T2 -> InfTau T2. 
cofix COFIX. 
intros.
inv H0. 
- assumption.
- inv H. 
  constructor. eapply COFIX; eauto.
Qed.

(********************** ObsTrace Equivalence *************************)

CoInductive ObsTraceEq(*_gen R*) : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsEqTau1 : forall OO OO'
                     (HR : (*R*)ObsTraceEq OO OO' : Prop),
                      (InfTau OO -> InfTau OO') ->  
    ObsTraceEq(*_gen R*) (notfinished Tau OO) OO'
| ObsEqTau2 : forall OO OO'
                     (HR : (*R*)ObsTraceEq OO OO' : Prop),
                      (InfTau OO' -> InfTau OO) ->  
    ObsTraceEq(*_gen R*) OO (notfinished Tau OO')
| ObsEqNow : forall w OO OO'
                     (HR : (*R*)ObsTraceEq OO OO' : Prop),
    ObsTraceEq(*_gen R*) (notfinished (Out w) OO) (notfinished (Out w) OO')
| ObsEqFinished : forall o,
    ObsTraceEq(*_gen R*) (finished o) (finished o)
.
Hint Constructors ObsTraceEq(*_gen*) : core.

Notation "OO' ~=_O OO" := (ObsTraceEq OO' OO) (at level 80).

Lemma ObsTraceEq_refl:
  forall O,
    O ~=_O O. 
Proof.
  cofix COFIX. 
  intros. 
  destruct O. 
  - constructor.
  - destruct o. 
    + constructor.  apply COFIX. 
    + constructor. constructor.  apply COFIX.
      auto.
      intro. constructor.  auto.
Qed.

Lemma ObsTraceEq_sym :
  forall O O',
    ObsTraceEq O O' -> ObsTraceEq O' O.
Proof.
  cofix COFIX.
  intros O O' H(*; pfold*).
  inv H;
    try (constructor; ((*right;*) apply COFIX; auto) || ((*left;*) auto)).
    (* Or, simplified, [constructor; auto]. *)
Qed.

Lemma ObsTraceEqRemoveTau1 :
  forall T T', ObsTraceEq (notfinished Tau T) T' -> ObsTraceEq T T'.
Proof.
  cofix COFIX.
  intros T T' Eq(*; pfold*).
  inv Eq.
  + (* RB: This goal is slightly more involved than it was before. *)
    (* apply paco2_unfold. *)
    (* * apply ObsTraceEq_mon. *)
    (* * apply paco2_mon_bot with ObsTraceEq_gen; auto. *)
    assumption.
  + eapply ObsEqTau2.
    (*right.*) eapply COFIX; auto.
    intro. apply H in H0.  inv H0.  apply H2. 
Qed.

Lemma ObsTraceEqRemoveTau2 :
  forall T T', ObsTraceEq T (notfinished Tau T') -> ObsTraceEq T T'.
Proof.
  cofix COFIX.
  intros T T' Eq(*; pfold*).
  inv Eq.
  + eapply ObsEqTau1.
    (*right.*) eapply COFIX.
    auto.
    intro.  apply H in H0.  inv H0.  apply H2. 
  +
    (* apply paco2_unfold. *)
    (* * apply ObsTraceEq_mon. *)
    (* * apply paco2_mon_bot with ObsTraceEq_gen; auto. *)
    assumption.
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

Lemma ObsTraceEq_InfTau' : forall T T',
   InfTau T' -> 
   T ~=_O T' -> 
   InfTau T.
Proof.
  cofix COFIX.
  intros.  
  inv H0. 
  - constructor. auto. eapply COFIX; eauto. 
  - inv H. apply H1.  apply H2. 
  - inv H. 
  - apply H. 
Qed.

Lemma ObsTraceEq_InfTau : forall T T',
    T ~=_O T' ->
    InfTau T <-> InfTau T'.
Proof.
  intros.
  split; intro.
  apply ObsTraceEq_sym in H. 
  eapply ObsTraceEq_InfTau'; eauto.
  eapply ObsTraceEq_InfTau'; eauto.
Qed.

(* Previous counter-example is gone, beause inftau is only related to itself,
   but I still can't prove transitivity. *)

Lemma ObsTraceEq_trans: forall T1 T2 T3,
    T1 ~=_O T2 -> 
    T2 ~=_O T3 -> 
    T1 ~=_O T3.
Proof.
  cofix COFIX.
  intros.
  inv H; inv H0; try (constructor; eauto;fail). 
  - apply ObsTraceEqRemoveTau2 in HR. 
    constructor; eauto. 
    intro. 
    apply H1 in H0.  inv H0.  apply H in H3.  auto.
  - constructor. constructor. 
    eapply COFIX; eauto. 
    intro. 
    apply H in H0. rewrite ObsTraceEq_InfTau; eauto.
    intro. constructor. apply H1 in H0.  rewrite ObsTraceEq_InfTau; eauto.
    apply ObsTraceEq_sym. auto.
  - constructor.  apply COFIX with (notfinished (Out w) OO0). apply HR.
    constructor. apply HR0.
    intro. apply H1 in H.  inv H. 
  - (* ObsEqTau2 meets ObsEqTau1 *) 
Abort.


(* Not clear if this is provable now. *)
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
      intros Eq1 O2' O2 Eq2(*;
      pfold*).
    + inversion Eq1; subst; simpl in *; clear Eq1; app_frobber.
      * destruct a.
        -- apply ObsEqNow; auto.
        -- apply ObsEqTau1. (*left. pfold.*) apply ObsEqTau2; auto.
           apply ObsTraceEq_InfTau; auto. 
           intro. constructor. auto. rewrite ObsTraceEq_InfTau; eauto.
           apply ObsTraceEq_sym. auto.
    + inversion Eq1; subst; simpl in *; clear Eq1.
      specialize (IHLast' HR O2' O2 Eq2).
      app_frobber.
      eapply ObsEqTau2.
      auto.
      admit. 
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq1) as [n [HTau | [T' HTau]]].
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber(*; pfold*).
        -- apply ObsEqNow.
           inversion Eq1.
        -- apply ObsEqTau2.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn H3 Eq1).
           auto.
           intro. 
           admit.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber(*; pfold*).
        -- apply ObsEqNow.
           inversion Eq1; subst; clear Eq1.
           (* RB: The following two subgoals become slightly different. *)
           ++ inversion Last'; subst; clear Last'.
              (*left.*)
              eapply IHLast; eauto.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn Eq1).
           apply ObsEqTau2.
           auto.
           admit.
    + apply ObsTraceEqRemoveTau1 in Eq1.
      app_frobber.
      (* RB: Ditto here, applying IH is now a bit more explicit. *)
      (*pfold.*) apply ObsEqTau1. (*left.*)
      eapply IHLast; eauto.
      admit.
Admitted. (* Qed. *)

(********************** ObsTrace Prefix *************************)
(* not at all sure about how to formulate this *)

CoInductive ObsTracePrefix(*_gen R*) : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsPreTau1 : forall OO OO'
                      (HR : (*R*)ObsTracePrefix OO OO' : Prop),
                      (InfTau OO -> InfTau  OO') -> 
    ObsTracePrefix(*_gen R*) (notfinished Tau OO) OO'
| ObsPreTau2 : forall OO OO'
                      (HR : (*R*)ObsTracePrefix OO OO' : Prop),
                      (InfTau OO' -> InfTau  OO) -> 
    ObsTracePrefix(*_gen R*) OO (notfinished Tau OO')
| ObsPreNow : forall w OO OO'
                      (HR : (*R*)ObsTracePrefix OO OO' : Prop),
    ObsTracePrefix(*_gen R*) (notfinished (Out w) OO) (notfinished (Out w) OO')
| ObsPreFinishedOut1 : forall o,
    ObsTracePrefix(*_gen R*) (finished o) (finished o)
| ObsPreFinishedOut2 : forall w OO,
    ObsTracePrefix(*_gen R*) (notfinished (Out w) OO) (finished (Out w))
| ObsPreFinishedTau : forall OO,
    ObsTracePrefix(*_gen R*) OO (finished Tau)
.
Hint Constructors ObsTracePrefix(*_gen*) : core.


Notation "OO' <=_O OO" := (ObsTracePrefix OO OO') (at level 80).

Lemma ObsTracePrefix_inftau0: inftau <=_O inftau. 
cofix COFIX. 
rewrite (idTrace_eq inftau). 
  simpl. 
  constructor. constructor.
  apply COFIX.
  auto.
  intro. constructor. assumption.
Qed.

Lemma ObsTracePrefix_refl : forall OO, ObsTracePrefix OO OO.
Proof.
  cofix CH.
  intros [o | o OO](*; pfold*).
  - constructor. 
  - destruct o as [w |].
    + apply ObsPreNow. now auto.
    + apply ObsPreTau2.  apply ObsPreTau1. apply CH.
      intro; auto.
      constructor. assumption.
Qed.

Lemma ObsTracePrefix_inftau : forall T T',
   InfTau T -> 
   T <=_O T' -> 
   InfTau T'.
Proof.
  cofix COFIX.
  intros.  
  inv H0. 
  - constructor.  eapply COFIX; eauto. 
  - inv H. apply H1. apply H2. 
  - inv H. 
  - apply H. 
  - inv H.  
  - inv H. 
Qed.


Lemma ObsTracePrefApp' :
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
      intros Eq O2' O2 Pref(*; pfold*).
    + inversion Eq; subst; simpl in *; clear Eq; app_frobber.
      (* Hint constructors doesn't work for this? *)
      * destruct a.
        -- apply ObsPreNow; auto.
        -- apply ObsPreTau2. (*left. pfold.*) apply ObsPreTau1; auto.
           intro. eapply ObsTracePrefix_inftau. eauto. (* oops *) admit. 
           admit.
    + inversion Eq; subst; simpl in *; clear Eq.
      specialize (IHLast' HR O2' O2 Pref).
      app_frobber.
      eapply ObsPreTau2.
      auto.
      admit.
  (* Try by inversion. *)
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq) as [n [HTau | [T' HTau]]](*;
        pfold*).
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
           admit.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsPreNow.
           inversion Eq; subst; clear Eq.
           (* RB: The following two subgoals become slightly different. *)
           ++ inversion Last'; subst; clear Last'.
              (*left.*)
              eapply IHLast; eauto.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn Eq).
           apply ObsPreTau2.
           auto.
           admit.
+ apply ObsTraceEqRemoveTau1 in Eq.
      app_frobber.
      (*pfold.*) apply ObsPreTau1. (*left.*)
      (* RB: Ditto here, applying IH is now a bit more explicit. *)
      eapply IHLast; eauto.
Admitted. (* Qed. *)


Lemma ObsTracePrefRemoveTau1 :
  forall T T', (notfinished Tau T) <=_O T' -> T <=_O T'.
Proof.
  cofix COFIX.
  intros T T' Pref(*; pfold*).
  inv Pref.
  + constructor. (*right.*) apply COFIX. auto. 
    intro. apply H in H0. inv H0. assumption.
  + auto.
Qed. 

Lemma ObsTracePrefRemoveTau2 :
  forall T T', T <=_O (notfinished Tau T') -> T <=_O T'.
Proof.
  cofix COFIX.
  intros T T' Pref.
  inv Pref.
  + assumption.
  + constructor. apply COFIX. auto.
    intro. apply H in H0.  inv H0.  assumption.
  + constructor. 
Qed.

Lemma ObsTracePrefFinished: forall OO, OO <=_O finished Tau -> OO ~=_O finished Tau.
Proof.
  cofix COFIX. 
  intros. 
  inv H.
  - constructor. apply COFIX; auto.
    intro.  auto.
  - constructor. 
  - constructor. 
Qed.


(** Alternative definition of ObsTraceEq. *)

Definition ObsTraceEq' OO OO' : Prop :=  ObsTracePrefix OO OO' /\ ObsTracePrefix OO' OO. 

Lemma OTE'E: forall T T', ObsTraceEq' T T' -> ObsTraceEq T T'. 
Proof.
  cofix COFIX.
  intros T T' [H1 H2].
  inv H1; inv H2; try apply ObsEqAllTau.  
  - apply ObsTracePrefRemoveTau1 in HR.  apply ObsTracePrefRemoveTau1 in HR0.  
    constructor. constructor. apply COFIX; split; auto.
    intro.  apply H0 in H1.  inv H1.  assumption. 
    intro.  apply H in H1.  inv H1.  constructor.  assumption. 
  - constructor.  apply COFIX; split;  auto.  auto.
  - constructor. apply COFIX; split; auto. auto.
  - apply ObsTracePrefRemoveTau2 in HR. apply ObsTracePrefRemoveTau2 in HR0. 
    constructor. constructor. apply COFIX; split; auto.
    intro. apply H in H1. inv H1. assumption. 
    intro. constructor. apply H0 in H1.  inv H1. assumption. 
  - constructor.
    apply ObsTracePrefFinished in HR. apply ObsTraceEq_sym. auto.
    intro. apply H in H0.  inv H0. 
  - constructor. apply COFIX; split; auto. 
  - constructor. 
  - constructor. 
  - apply ObsTracePrefFinished in HR. constructor. auto. intro.
    apply H in H0. inv H0. 
  - constructor.
  - constructor. 
Qed.

Lemma OTEE'1 : forall T T', ObsTraceEq T T' -> ObsTracePrefix T T'. 
Proof.
  cofix COFIX. 
  intros. 
  inv H; try (constructor; eauto).  
Qed.


Lemma OTEE': forall T T', ObsTraceEq T T' -> ObsTraceEq' T T'. 
Proof.
  intros.
  split.
  apply OTEE'1; auto. 
  apply ObsTraceEq_sym in H. 
  apply OTEE'1;  auto. 
Qed.


(* no longer works...

Module ObsTraceRelsNotTrans.

CoFixpoint inftau : ObsTrace := notfinished Tau inftau.

(* now false *)
Lemma inftau1 : forall w, finished (Out w) <=_O inftau.
cofix COFIX.
intros.
  rewrite (idTrace_eq inftau).  simpl. 
  constructor. apply COFIX.
Abort. 

(* also false *)
Lemma inftau2 : forall w, inftau <=_O finished(Out w). 
cofix COFIX. 
intros.
  rewrite (idTrace_eq inftau).  simpl. 
  constructor. apply COFIX.
Abort.

Section foo.
Hypothesis ws: exists (w1 w2: Word), w1 <> w2. 

Lemma ObsTracePrefix_not_transitive: exists T1 T2 T3,
    T1 <=_O T2 /\ T2 <=_O T3 /\ ~ (T1 <=_O T3). 
Proof.
  destruct ws as [w1 [w2 NEQ]].
  exists (finished (Out w1)).
  exists inftau.
  exists (finished (Out w2)).
  split.
  apply inftau1. 
  split.
  apply inftau2.
  intro.
  inv H. 
  apply NEQ; auto.
Qed.

Lemma ObsTraceEq_not_transitive: exists T1 T2 T3,
    T1 ~=_O T2 /\ T2 ~=_O T3 /\ ~ (T1 ~=_O T3). 
Proof.
  destruct ws as [w1 [w2 NEQ]].
  exists (finished (Out w1)).
  exists inftau.
  exists (finished (Out w2)).
  split.
  apply OTE'E. unfold ObsTraceEq'. split.
  apply inftau2. 
  apply inftau1.
  split.
  apply OTE'E. unfold ObsTraceEq'. split.
  apply inftau1.
  apply inftau2.
  intro.
  inv H. 
  apply NEQ; auto.
Qed.

End foo.

End ObsTraceRelsNotTrans.

 *)

Lemma ObsTracePrefix_trans: forall T1 T2 T3, T1 <=_O T2 -> T2 <=_O T3 -> T1 <=_O
 T3.
Proof.
  cofix COFIX.
  intros. 
  inv H; inv H0; try (constructor; eauto; fail).
  - constructor. apply ObsTracePrefRemoveTau1 in HR0. 
    apply COFIX with OO; auto. 
    intro. apply H in H0. inv H0.  apply H1 in H3.  assumption. 
  - admit.  (* no forward progress *)
  - constructor. constructor.
    apply COFIX with T2; auto. 
    + admit. (* oops *)
    + admit. (* oops *)
  - constructor. 
    + apply COFIX with (notfinished Tau OO'0). 
      * assumption. 
      * constructor. assumption. apply H. 
    + intro. apply H1 in H0. inv H0. apply H; auto.
  -  constructor. apply COFIX with (notfinished (Out w) OO'0).
     assumption.
     constructor. assumption.
     intro. apply H1 in H. inv H. 
  - constructor. apply COFIX with (finished (Out w)).
    assumption.
    constructor.
    intro.  apply H1 in H. inv H. 
  - constructor. 
    apply COFIX with (finished Tau).
    assumption. constructor.
    intro.  apply H1 in H.  inv H. 
  - constructor. 
    apply COFIX with (notfinished (Out w) OO).
    constructor.  assumption.
    assumption.
    intro.
    apply H in H0. inv H0. 
  - constructor. 
    apply COFIX with (notfinished (Out w) OO).
    constructor. 
    assumption.
    intro. apply H in H0. 
    inv H0. 
Abort.


(********************** Relationship betweeen Traces and ObsTraces  *************************)


Lemma TraceEqImpliesObsTraceEq :
  forall O O',
    O ~= O' ->
    ObsTraceEq O O'.
Proof. 
  cofix COFIX. intros O O' H(*; pfold*). inv H.
  - constructor.
  - destruct a.
    + constructor.  auto. 
    + constructor. (*left. pfold.*) constructor. auto. 
      apply ObsTraceEq_InfTau. auto. 
      intro.  constructor. rewrite ObsTraceEq_InfTau; eauto. apply ObsTraceEq_sym.
      auto.
(* oops: just a technical issue ? *)
Abort.

Lemma ObsTraceEqImpliesPrefix :
  forall O O',
    ObsTraceEq O O' ->
    O <=_O O'.
Proof.
  cofix COFIX. intros O O' H. (*pfold.*)
  inv H; constructor; try (*right;*) apply COFIX; auto.
Qed.

    
Lemma ObsPrefOverEq :
  forall O1 O1' O2,
    O1 ~= O1' ->
    O1 <=_O O2 ->
    O1' <=_O O2.
Proof.
  cofix COFIX. intros O1 O1' O2 H H0(*; pfold*). inv H.
  - assumption.
    (* apply paco2_unfold. *)
    (* + auto with paco. *)
    (* + eapply paco2_mon_bot; eauto with paco. *)
  - destruct a.
    + inv H0.
      * constructor. (*right.*)
        apply (COFIX (notfinished (Out w) T1) (notfinished (Out w) T2) OO).
        -- (*pfold.*) constructor. auto.
        -- auto.
        -- intro.  apply H in H0.  inv H0. 
      * constructor. (*right.*) apply (COFIX T1 T2 OO); auto.
    + constructor. (*right.*) apply (COFIX T1 T2 O2); auto. apply ObsTracePrefRemoveTau1. 
      auto. 
      intro.
      inv H0. 
      * constructor.  
        eapply ObsTracePrefix_inftau with (notfinished Tau T1). 
        -- constructor. 
           assert (InfTau (notfinished Tau T1)).
           { apply H2. 
             eapply ObsTracePrefix_inftau. 
             2: { apply HR.  }
             constructor.
             eapply inftaueq. apply H. symmetry. assumption. }
           inv H0. assumption.
        -- assumption.
      * apply H4.  eapply inftaueq; eauto.  symmetry;assumption.
Qed.


Lemma ObsEqOverEq :
  forall O1 O1' O2,
    O1 ~= O1' ->
    ObsTraceEq O1 O2 ->
    ObsTraceEq O1' O2.
Proof.
  cofix COFIX. intros O1 O1' O2 H H0(*; pfold*). inv H.
  - assumption.
    (* apply paco2_unfold. *)
    (* * auto with paco. *)
    (* * eapply paco2_mon_bot; eauto with paco. *)
  - destruct a.
    + inv H0.
      * constructor. (*right.*)
        apply (COFIX (notfinished (Out w) T1) (notfinished (Out w) T2) OO').
        -- (*pfold.*) constructor. auto.
        -- auto.
        -- intro. apply H in H0.  inv H0. 
      * constructor. (*right.*) apply (COFIX T1 T2 OO'); auto.
    + constructor. (*right.*) apply (COFIX T1 T2 O2); auto. apply ObsTraceEqRemoveTau1. auto.
      intro. 
      inv H0. 
      * apply H3.  eapply inftaueq; eauto. symmetry. auto.
      * constructor. eapply (ObsTraceEq_InfTau _ _ HR).
        constructor. eapply inftaueq; eauto.  symmetry. auto. 
Qed.
