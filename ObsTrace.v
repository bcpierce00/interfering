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

CoInductive ObsTraceEq(*_gen R*) : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsEqTau1 : forall OO OO'
                     (HR : (*R*)ObsTraceEq OO OO' : Prop),
    ObsTraceEq(*_gen R*) (notfinished Tau OO) OO'
| ObsEqTau2 : forall OO OO'
                     (HR : (*R*)ObsTraceEq OO OO' : Prop),
    ObsTraceEq(*_gen R*) OO (notfinished Tau OO')
| ObsEqNow : forall w OO OO'
                     (HR : (*R*)ObsTraceEq OO OO' : Prop),
    ObsTraceEq(*_gen R*) (notfinished (Out w) OO) (notfinished (Out w) OO')
(*
| ObsEqFinishedOut : forall w,
    ObsTraceEq(*_gen R*) (finished (Out w)) (finished (Out w))
| ObsEqFinishedTau :
    ObsTraceEq(*_gen R*) (finished Tau) (finished Tau)
 *)
(* The last thing we need is a way of handling *all-tau* traces.
   There are a couple of ways of doing that, not sure what will
   play better in proofs. *)
| ObsEqAllSame : forall OO,
     ObsTraceEq(*_gen R*) OO OO.
(* APT: Establishing equality between traces seems hard, and this overlaps
the previous two cases.  Maybe try:
   ForallTrace (fun o => o = Tau) OO ->
   ForallTrace (fun o => o = Tau) OO' ->
   ObsTraceEq OO OO'
?
LEO: That was the other thing I had in mind. I'll see what makes proofs easier.
(Note that this proposal overlaps with the first two cases, as well as the last one.)
 *)
Hint Constructors ObsTraceEq(*_gen*) : core.

(* Definition ObsTraceEq (OO OO' : TraceOf Observation) := *)
(*   paco2 ObsTraceEq_gen bot2 OO OO'. *)
(* Hint Unfold ObsTraceEq : core. *)
(* Lemma ObsTraceEq_mon : monotone2 ObsTraceEq_gen. Proof. pmonauto. Qed. *)
(* Hint Resolve ObsTraceEq_mon : paco. *)

Notation "OO' ~=_O OO" := (ObsTraceEq OO' OO) (at level 80).

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
  + eapply ObsEqTau2.
    (*left. pfold.*) eapply ObsEqAllSame.
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
  + (* RB: This goal is slightly more involved than it was before. *)
    (* apply paco2_unfold. *)
    (* * apply ObsTraceEq_mon. *)
    (* * apply paco2_mon_bot with ObsTraceEq_gen; auto. *)
    assumption.
  + eapply ObsEqTau1. (*left. pfold.*)
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
      intros Eq1 O2' O2 Eq2(*;
      pfold*).
    + inversion Eq1; subst; simpl in *; clear Eq1; app_frobber.
      * destruct a.
        -- apply ObsEqNow; auto.
        -- apply ObsEqTau1. (*left. pfold.*) apply ObsEqTau2; auto.
    + inversion Eq1; subst; simpl in *; clear Eq1.
      specialize (IHLast' HR O2' O2 Eq2).
      app_frobber.
      eapply ObsEqTau2.
      auto.
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
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber(*; pfold*).
        -- apply ObsEqNow.
           inversion Eq1; subst; clear Eq1.
           (* RB: The following two subgoals become slightly different. *)
           ++ inversion Last'; subst; clear Last'.
              (*left.*)
              eapply IHLast; eauto.
           ++ inversion Last'; subst; clear Last'.
              (*left.*)
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
      (*pfold.*) apply ObsEqTau1. (*left.*)
      eapply IHLast; eauto.
Qed.

(********************** ObsTrace Prefix *************************)

(* LEO: I didn't like the non-coinductive nature of this... 
Definition ObsTracePrefix (OO OO' : TraceOf Observation) : Prop :=
  exists OO'', ObsTraceEq OO OO'' /\ OO' <<== OO'' \/ ObsTraceEq OO' OO'' /\ OO' <<== OO.
 *)

(* The second is a prefix of the first, up to Tau *)
CoInductive ObsTracePrefix(*_gen R*) : TraceOf Observation -> TraceOf Observation -> Prop :=
| ObsPreTau1 : forall OO OO'
                      (HR : (*R*)ObsTracePrefix OO OO' : Prop),
    ObsTracePrefix(*_gen R*) (notfinished Tau OO) OO'
| ObsPreTau2 : forall OO OO'
                      (HR : (*R*)ObsTracePrefix OO OO' : Prop),
    ObsTracePrefix(*_gen R*) OO (notfinished Tau OO')
| ObsPreNow : forall w OO OO'
                      (HR : (*R*)ObsTracePrefix OO OO' : Prop),
    ObsTracePrefix(*_gen R*) (notfinished (Out w) OO) (notfinished (Out w) OO')
(*| ObsPreFinishedOut1 : forall w,
    ObsTracePrefix(*_gen R*) (finished (Out w)) (finished (Out w))
*)
| ObsPreFinishedOut2 : forall w OO,
    ObsTracePrefix(*_gen R*) (notfinished (Out w) OO) (finished (Out w))
| ObsPreFinishedTau : forall OO,
    ObsTracePrefix(*_gen R*) OO (finished Tau)
| ObsPreAllSame : forall OO,
     ObsTracePrefix(*_gen R*) OO OO.
Hint Constructors ObsTracePrefix(*_gen*) : core.

(* Definition ObsTracePrefix (OO OO' : TraceOf Observation) := *)
(*   paco2 ObsTracePrefix_gen bot2 OO OO'. *)
(* Hint Unfold ObsTracePrefix : core. *)
(* Lemma ObsTracePrefix_mon : monotone2 ObsTracePrefix_gen. Proof. pmonauto. Qed. *)
(* Hint Resolve ObsTracePrefix_mon : paco. *)

Notation "OO' <=_O OO" := (ObsTracePrefix OO OO') (at level 80).

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
        -- apply ObsPreTau1. (*left. pfold.*) apply ObsPreTau2; auto.
    + inversion Eq; subst; simpl in *; clear Eq.
      specialize (IHLast' HR O2' O2 Pref).
      app_frobber.
      eapply ObsPreTau2.
      auto.
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
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; app_frobber.
        -- apply ObsPreNow.
           inversion Eq; subst; clear Eq.
           (* RB: The following two subgoals become slightly different. *)
           ++ inversion Last'; subst; clear Last'.
              (*left.*)
              eapply IHLast; eauto.
           ++ inversion Last'; subst; clear Last'.
              (*left.*)
              eapply IHLast; eauto.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn Eq).
           apply ObsPreTau2.
           auto.
    + apply ObsTraceEqRemoveTau1 in Eq.
      app_frobber.
      (*pfold.*) apply ObsPreTau1. (*left.*)
      (* RB: Ditto here, applying IH is now a bit more explicit. *)
      eapply IHLast; eauto.
Qed.

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
  intros T T' Pref(*; pfold*).
  inv Pref.
  + constructor. (*right.*) apply COFIX. auto.
  + (* RB: Some base cases like this need a little more work than before. *)
    (* apply paco2_unfold. *)
    (* * auto with paco. *)
    (* * eapply paco2_mon_bot; eauto with paco. *)
    assumption.
  + constructor. (*left.
    eapply paco2_mon_bot with ObsTracePrefix_gen; [| auto].*)
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

(** Alternative definition of ObsTraceEq. *)

Definition ObsTraceEq' OO OO' : Prop :=  ObsTracePrefix OO OO' /\ ObsTracePrefix OO' OO. 

Lemma OTE'E: forall T T', ObsTraceEq' T T' -> ObsTraceEq T T'. 
Proof.
  cofix COFIX.
  intros T T' [H1 H2].
  inv H1; inv H2; try apply ObsEqAllSame.  
  - apply ObsTracePrefRemoveTau1 in HR.  apply ObsTracePrefRemoveTau1 in HR0.  
    constructor. constructor. apply COFIX; split; auto.
  - constructor.  apply COFIX; split;  auto. 
  - constructor. apply COFIX; split; auto.
  - apply ObsTracePrefRemoveTau2 in HR. apply ObsTracePrefRemoveTau2 in HR0. 
    constructor. constructor. apply COFIX; split; auto.
  - constructor.
    apply ObsTracePrefFinished in HR. apply ObsTraceEq_sym. auto.
  - constructor. apply COFIX; split; auto. 
  - constructor. 
    apply ObsTracePrefFinished in HR. auto.
Qed.

Lemma OTEE'1 : forall T T', ObsTraceEq T T' -> ObsTracePrefix T T'. 
Proof.
  cofix COFIX. 
  intros. 
  inv H; constructor; eauto.  
Qed.

Lemma OTEE'2 : forall T T', ObsTraceEq T T' -> ObsTracePrefix T' T. 
Proof.
  cofix COFIX. 
  intros. 
  inv H; constructor; eauto.  
Qed.

Lemma OTEE': forall T T', ObsTraceEq T T' -> ObsTraceEq' T T'. 
Proof.
  intros.
  split.
  apply OTEE'1; auto. 
  apply OTEE'2;  auto. 
Qed.


(********************** Relationship betweeen Traces and ObsTraces  *************************)


Lemma TraceEqImpliesObsTraceEq :
  forall O O',
    O ~= O' ->
    ObsTraceEq O O'.
Proof.
  cofix COFIX. intros O O' H(*; pfold*). inv H.
  - constructor.
  - destruct a.
    + constructor. auto.
    + constructor. (*left. pfold.*) constructor. auto.
Qed.

Lemma ObsTraceEqImpliesPrefix :
  forall O O',
    ObsTraceEq O O' ->
    O <=_O O'.
Proof.
  cofix COFIX. intros O O' H. (*pfold.*)
  inv H; constructor; (*right;*) apply COFIX; auto.
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
      * constructor. (*right.*) apply (COFIX T1 T2 OO); auto.
      * constructor.
        (* left. *)
        (* apply paco2_mon_bot with ObsTracePrefix_gen; [| auto]. *)
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
        apply (COFIX OO' (notfinished (Out w) T1) (notfinished (Out w) T2)).
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
    (* apply paco2_unfold. *)
    (* * auto with paco. *)
    (* * eapply paco2_mon_bot; eauto with paco. *)
  - destruct a.
    + inv H0.
      * constructor. (*right.*)
        apply (COFIX (notfinished (Out w) T1) (notfinished (Out w) T2) OO').
        -- (*pfold.*) constructor. auto.
        -- auto.
      * constructor. (*right.*) apply (COFIX T1 T2 OO'); auto.
      * constructor.
        (* left. *)
        (* apply paco2_mon_bot with ObsTraceEq_gen; [| auto]. *)
        apply ObsTraceEq_sym. apply TraceEqImpliesObsTraceEq. auto.
    + constructor. (*right.*) apply (COFIX T1 T2 O2); auto. apply ObsTraceEqRemoveTau1. auto.
Qed.

(***** Taking ObsTraces from traces and runs *****)

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

Definition ObsOfMP (MPO : MPTrace') : TraceOf Observation :=
  mapTrace snd MPO.

Definition ObsOfM (MO : MTrace') : TraceOf Observation :=
  mapTrace snd MO.

(***** Lemmas about JoinInclusive on ObsTraces *****)

Definition ObsOfMPJoin :
  forall MPO MPO',
    ObsOfMP (MPO ^^ MPO') ~= (ObsOfMP MPO ^^ ObsOfMP MPO').
Proof.
  unfold ObsOfMP. apply MapOverJoin.
Qed.

Definition ObsOfMJoin :
  forall MO MO',
    ObsOfM (MO ^^ MO') ~= (ObsOfM MO ^^ ObsOfM MO').
Proof.
  unfold ObsOfM. apply MapOverJoin.
Qed.

Lemma ObsEqJoin :
  forall O1 O1' O2 O2' o1 o1',
    Last O1 o1 ->
    Last O1' o1' ->
    O1 ~=_O O1' ->
    O2 ~=_O O2' ->
    (O1 ^^ O2) ~=_O (O1' ^^ O2').
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
    + inversion Eq1; subst; simpl in *; clear Eq1; join_frobber.
      destruct O2; destruct O2'; auto.
    + inversion Eq1; subst; simpl in *; clear Eq1.
      specialize (IHLast' HR O2' O2 Eq2).
      join_frobber.
      eapply ObsEqTau2.
      auto.
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq1) as [n [HTau | [T' HTau]]].
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; join_frobber.
        -- inversion Eq1.
        -- apply ObsEqTau2.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq1.
           specialize (IHn H3 Eq1).
           auto.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; join_frobber.
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
      join_frobber. apply ObsEqTau1.
      eapply IHLast; eauto.
Qed.


Lemma ObsPrefJoin :
  forall O1 O1' O2 O2' o1 o1',
    Last O1 o1 ->
    Last O1' o1' ->
    O1 ~=_O O1' ->
    O2 <=_O O2' ->
    (O1 ^^ O2) <=_O (O1' ^^ O2').
Proof.
    intros O1 O1' O2 O2' o1 o1' H;
    revert O1' O2 O2' o1'.
  induction H as [o1|]; intros O1' O2 O2' o1' Last' Eq Pref.
  - generalize dependent O2;
    generalize dependent O2';
    generalize dependent Eq.
    induction Last';
      intros Eq O2' O2 Pref.
    + inversion Eq; subst; simpl in *; clear Eq; join_frobber.
      destruct O2; destruct O2'; auto.
    + inversion Eq; subst; simpl in *; clear Eq.
      specialize (IHLast' HR O2' O2 Pref).
      join_frobber.
      eapply ObsPreTau1.
      auto.
  - destruct a'.
    + destruct (EqOut_tauN O1' o1' Last' w T Eq) as [n [HTau | [T' HTau]]].
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; join_frobber.
        -- inversion Eq.
        -- apply ObsPreTau1.
           inversion Last'; subst; clear Last'.
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn H3 Eq).
           auto.
      * rewrite HTau in *.
        clear HTau.
        induction n; simpl in *; subst; join_frobber.
        -- apply ObsPreNow.
           inversion Eq; subst; clear Eq.
           ++ inversion Last'; subst; clear Last'.
              eapply IHLast; eauto.
           ++ inversion Last'; subst; clear Last'.
              eapply IHLast; eauto.
        -- inversion Last'; subst; clear Last'.
           specialize (IHn H3).
           apply ObsTraceEqRemoveTau2 in Eq.
           specialize (IHn Eq).
           apply ObsPreTau1.
           auto.
    + apply ObsTraceEqRemoveTau1 in Eq.
      join_frobber. apply ObsPreTau2.
      eapply IHLast; eauto.
Qed.

Lemma MPRunPrefRun :
  forall mp m,
     ms mp = m -> 
     ObsOfMP (MPRunOf mp) <=_O ObsOfM (RunOf m).
Proof.
  cofix COFIX.
  intros mp m H(*; pfold*).
  destruct mp. simpl in *.  subst.
  rewrite idTrace_eq. pattern (ObsOfM (RunOf m)) at 1.  rewrite idTrace_eq.  simpl.
  destruct (pstep (m,p)); simpl.
  - destruct (step m).  simpl.
    destruct o. 
    * constructor. (*right.*) apply COFIX. auto.
    * constructor. (*left. pfold.*) constructor. (*right.*) apply COFIX. auto.
  - destruct (step m). simpl.
    constructor.
Qed.

Lemma RunEqInfMPRun :
  forall mp m,
    ms mp = m ->
    infinite (MPRunOf mp) ->
    (ObsOfMP (MPRunOf mp)) ~=_O (ObsOfM (RunOf m)).
Proof.
  cofix COFIX.
  intros mp m H H0(*; pfold*).
  destruct mp. simpl in *. subst.
  rewrite idTrace_eq. rewrite (idTrace_eq (ObsOfMP (MPRunOf (m,p)))).  simpl.
  destruct (pstep (m,p)) eqn:?; simpl.
  - destruct (step m) eqn:?.  simpl.
    assert (Q: infinite (MPRunOf (m0, p0))).
    { intro. intro. unfold infinite in H0.
      apply (H0 a).
      rewrite (idTrace_eq (MPRunOf (m,p))). simpl.
      rewrite Heqo. rewrite Heqp1.  simpl.
      constructor.  auto. }
    destruct o.
    + constructor. (*right.*) apply COFIX; auto.
    + constructor. (*left. pfold.*) constructor. (*right.*) apply COFIX; auto.
  - exfalso. unfold infinite in H0. eapply (H0 (m,p,Tau)).
    rewrite (idTrace_eq (MPRunOf (m,p))).  simpl.
    rewrite Heqo.
    constructor.
Qed.
