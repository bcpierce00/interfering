Require Export Setoid.
Require Coq.Classes.RelationClasses.
(*Require Import Paco.paco.*)

(* Attempt to perform Paco inversion first. For non-Paco definitions, this fails
   and falls back on regular inversion. The order of this operation is
   important. *)
Ltac inv H := (*(pinversion H ||*) inversion H(*)*); subst; clear H.

CoInductive TraceOf (A : Type) : Type :=
| finished : A -> TraceOf A
| notfinished : A -> TraceOf A -> TraceOf A.

Arguments finished {_} _.
Arguments notfinished {_} _ _.

Definition idTrace {A} (T: TraceOf A) : TraceOf A :=
  match T with
  | finished a => finished a
  | notfinished a T' => notfinished a T'
  end.

Lemma idTrace_eq : forall {A} (T: TraceOf A), T = idTrace T.
   destruct T; reflexivity.
Qed.

Definition head {A} (T : TraceOf A) : A :=
  match T with
  | finished T => T
  | notfinished T _ => T
  end.

Inductive InTrace {A} (a:A) : TraceOf A -> Prop :=
| In_finished : InTrace a (finished a)
| In_now : forall T, InTrace a (notfinished a T)
| In_later : forall a' T, InTrace a T -> InTrace a (notfinished a' T).

Lemma head_InTrace :forall {A} (T: TraceOf A), InTrace (head T) T.
Proof.
  intros.
  destruct T.
  - constructor.
  - simpl. constructor.
Qed.

CoFixpoint mapTrace {A B:Type} (f:A -> B) (T: TraceOf A) : TraceOf B :=
  match T with
  | finished a => finished (f a)
  | notfinished a T' => notfinished (f a) (mapTrace f T')
  end.

CoInductive TraceEq(*_gen*) {A} (*R*) : TraceOf A -> TraceOf A -> Prop :=
| EqFin : forall a, TraceEq(*_gen R*) (finished a) (finished a)
| EqCons : forall a T1 T2,
    (*R*)TraceEq T1 T2 -> TraceEq(*_gen R*) (notfinished a T1) (notfinished a T2).
(* Hint Constructors TraceEq_gen : core. *)

(* Definition TraceEq {A} (T1 T2 : TraceOf A) := paco2 TraceEq_gen bot2 T1 T2. *)
(* Hint Unfold TraceEq : core. *)
(* Lemma TraceEq_mon A : monotone2 (@TraceEq_gen A). Proof. pmonauto. Qed. *)
(* Hint Resolve TraceEq_mon : paco. *)

Notation "T1 ~= T2" := (TraceEq T1 T2) (at level 80).

Lemma TraceEqRefl: forall {A} (T: TraceOf A),
    TraceEq T T.
Proof.
  intro A.
  cofix COFIX.
  intro T(*; pfold*).
  destruct T.
  - constructor.
  - constructor. (*right.*) apply COFIX.
Qed.

Lemma TraceEqTrans : forall {A} (T1 T2 T3: TraceOf A),
    TraceEq T1 T2 ->
    TraceEq T2 T3 ->
    TraceEq T1 T3. 
Proof.
  intro A.
  cofix COFIX.
  intros T1 T2 T3 H H0(*; pfold*).
  inversion H; subst.
  - inversion H0; subst.
    constructor. 
  - inversion H0; subst.
    constructor. (*right.*) eapply COFIX; eauto.
Qed.

Lemma TraceEqSym : forall {A} (T1 T2: TraceOf A),
    TraceEq T1 T2 ->
    TraceEq T2 T1.
Proof.
  intro A.
  cofix COFIX.
  intros T1 T2 H(*; pfold*).
  inversion H; subst.
  - constructor.
  - constructor. (*right.*) apply COFIX; auto.
Qed.

Add Parametric Relation A : (TraceOf A) (@TraceEq A)
    reflexivity proved by (TraceEqRefl (A := A))
    symmetry proved by (TraceEqSym (A := A))                            
    transitivity proved by (TraceEqTrans (A := A))
as TraceEq_rel                             
.                                        

Lemma TraceEqHead : forall {A} (T1 T2: TraceOf A), TraceEq T1 T2 -> head T1 = head T2. 
Proof.
  intros A T1 T2 H. destruct H; auto.
Qed.

Add Parametric Morphism A: (@head A)
   with signature (@TraceEq A) ==> (@eq A) as head_mor.                             
Proof.
  exact (@TraceEqHead A). 
Qed.   

CoFixpoint TraceApp {A} (T: TraceOf A) (TO: option (TraceOf A)) : TraceOf A :=
  match T with
  | finished a =>
    match TO with
    | Some a' => notfinished a a'
    | None => T
    end
  | notfinished a T' => notfinished a (TraceApp T' TO)
  end.

Notation "T1 ^ T2" := (TraceApp T1 T2).

Definition OpTraceEq {A} (TO1 TO2 : option(TraceOf A)) : Prop :=
  match TO1,TO2 with
  | None,None => True
  | Some T1, Some T2 => TraceEq T1 T2
  | _,_ => False
  end.
                                
Lemma OpTraceEqRefl {A} : forall (T: option(TraceOf A)), OpTraceEq T T.
Proof.
  unfold OpTraceEq; destruct T; auto. reflexivity.
Qed.

Lemma OpTraceEqSym {A} : forall (T1 T2: option(TraceOf A)), OpTraceEq T1 T2 -> OpTraceEq T2 T1.
Proof.
  intros.
  unfold OpTraceEq in * ; destruct T1, T2; auto. symmetry; auto. 
Qed.

Lemma OpTraceEqTrans {A} : forall (T1 T2 T3: option(TraceOf A)),
    OpTraceEq T1 T2 ->
    OpTraceEq T2 T3 ->
    OpTraceEq T1 T3.
Proof.
  intros.
  unfold OpTraceEq in * ; destruct T1, T2, T3; auto. eapply TraceEqTrans; eauto. inversion H. 
Qed.


Add Parametric Relation A : (option(TraceOf A)) (@OpTraceEq A)
    reflexivity proved by (OpTraceEqRefl (A := A))
    symmetry proved by (OpTraceEqSym (A := A))                            
    transitivity proved by (OpTraceEqTrans (A := A))
as OpTraceEq_rel                             
.                                        

Lemma TraceAppEq {A} : 
      forall (T1 T1' : TraceOf A) ,
        TraceEq T1 T1' ->
       forall (TO2 TO2': option(TraceOf A)),
        OpTraceEq TO2 TO2' ->
        TraceEq (T1 ^ TO2) (T1' ^ TO2'). 
Proof.
  cofix COFIX.
  intros T1 T1' H TO2 TO2' H1(*; pfold*).
  inv H.
  - rewrite idTrace_eq. rewrite (idTrace_eq (finished a ^ TO2)). simpl.
    destruct TO2, TO2'; simpl in H1.
    + inv H1.
      * constructor; auto. apply TraceEqRefl.
      * constructor. (*left.
        pfold. right.
        apply upaco2_mon_bot with TraceEq_gen; auto.*)
        constructor. assumption.
    + inversion H1.
    + inversion H1.
    + constructor.
  - rewrite idTrace_eq. rewrite (idTrace_eq (notfinished a T0 ^ TO2)). simpl.
    constructor. (*right.*) apply COFIX; auto.
Qed.

Add Parametric Morphism A: (@TraceApp A)
   with signature (@TraceEq A) ==> (@OpTraceEq A) ==> (@TraceEq A) as app_mor.
Proof.
  exact (@TraceAppEq A).
Qed.

Lemma TraceAppHead {A} :
  forall (T1 T2 : TraceOf A) (TO : option (TraceOf A)),
    T1 = T2 ^ TO -> head T1 = head T2.
Proof.
  intros T1 T2 TO App.
  destruct T2 as [a | a T2'].
  - rewrite App.
    simpl.
    destruct TO; simpl; auto.
  - rewrite App.
    simpl.
    auto.
Qed.

Lemma TraceAppHead' {A} :
  forall (T1 T2 : TraceOf A) (TO : option (TraceOf A)),
    TraceEq T1 (T2 ^ TO) -> head T1 = head T2.
Proof.
  intros T1 T2 TO App.
  rewrite App.
  destruct T2 as [a | a T2'].
  -  simpl. 
    destruct TO; simpl; auto.
  - simpl.
    auto.
Qed.

Lemma TraceAppNone :
  forall {A} (T : TraceOf A),
    TraceEq T (T^None).
Proof.
  intro A. cofix COFIX. intros(*; pfold*). rewrite idTrace_eq. destruct T.
  - simpl. constructor.
  - simpl. constructor. (*right.*) apply COFIX.
Qed.

Lemma TraceAppAssoc :
  forall A (T1 T2 : TraceOf A) TO,
    T1 ^ Some (T2 ^ TO) ~= (T1 ^ Some T2) ^ TO.
Proof.
  intro A. cofix COFIX.
  intros(*; pfold*).
  destruct T1.
  - rewrite idTrace_eq.  rewrite idTrace_eq at 1. simpl.
    constructor. (*left. apply paco2_mon_bot with TraceEq_gen; [| auto].*) apply TraceEqRefl.
  - rewrite idTrace_eq.  rewrite (idTrace_eq (notfinished a T1 ^ Some (T2 ^ TO))). simpl.
    constructor.
    (*right.*) apply COFIX.
Qed.

(* TracePrefix T1 T2 says T2 is a prefix of T1. *)
Definition TracePrefix {A} (T1 T2: TraceOf A): Prop :=
  exists TO,
    TraceEq T1 (T2^TO).

Notation "T2 <<== T1" := (TracePrefix T1 T2) (at level 80).

Lemma TracePrefix_refl :
  forall {A} (T:TraceOf A),
    T <<== T.
Proof.
  intros. exists None. apply TraceAppNone.
Qed.

Lemma TracePrefix_trans:
  forall {A} (T1 T2 T3: TraceOf A),
     T2 <<== T1 -> T3 <<== T2 -> T3 <<== T1.
Proof.
  intros.
  destruct H as [TO P].  destruct H0 as [TO' P'].
  rewrite P' in P.
  destruct TO, TO'. 
  - rewrite <- TraceAppAssoc in P. 
    eexists; eauto. 
  - rewrite <- TraceAppNone in P. 
    eexists; eauto.
  - rewrite <- TraceAppNone in P. 
    eexists; eauto.
  - repeat rewrite <- TraceAppNone in P. 
    eexists. 
    rewrite <- TraceAppNone. auto.
Qed.


Add Parametric Relation A : (TraceOf A) (@TracePrefix A)
    reflexivity proved by (TracePrefix_refl (A := A))
    transitivity proved by (TracePrefix_trans (A := A))
as TracePrefix_rel                             
.                                        

Lemma TracePrefixEq {A}: 
      forall (T1 T1' : TraceOf A) ,
        TraceEq T1 T1' ->
      forall (T2 T2' : TraceOf A) ,
        TraceEq T2 T2' ->
        TracePrefix T1 T2 ->
        TracePrefix T1' T2'. 
Proof.
  unfold TracePrefix. 
  intros. 
  destruct H1 as [TO P]. 
  exists TO.
  rewrite <- H. rewrite <- H0. auto.
Qed.

Add Parametric Morphism A: (@TracePrefix A)
    with signature (@TraceEq A) ==> (@TraceEq A) ==> Basics.impl as pref_mor.
Proof.
  exact (@TracePrefixEq A).                                                                                     Qed.                            
                             
CoInductive ForallTrace(*_gen*) {A : Type} (P : A -> Prop) (*R*) : TraceOf A -> Prop :=
| Forall_finished : forall a,
    P a -> ForallTrace(*_gen*) P (*R*) (finished a)
| Forall_notfinished : forall a T',
    P a -> (*R*)ForallTrace P T' -> ForallTrace(*_gen*) P (*R*) (notfinished a T').
(* Hint Constructors ForallTrace_gen : core. *)

(* Definition ForallTrace {A} (P : A -> Prop) (T : TraceOf A) := *)
(*   paco1 (ForallTrace_gen P) bot1 T. *)
(* Hint Unfold ForallTrace : core. *)
(* Lemma ForallTrace_mon A P : monotone1 (@ForallTrace_gen A P). Proof. pmonauto. Qed. *)
(* Hint Resolve ForallTrace_mon : paco. *)

Lemma ForallInTrace :
  forall {A} (f:A->Prop) T t,
    InTrace t T ->
    ForallTrace f T ->
    f t.
Proof.
  intros. induction H; inversion H0; auto.
Qed.

Lemma ForallTraceTautology :
  forall {A} (P:A->Prop) (T:TraceOf A),
    (forall a, P a) -> ForallTrace P T.
Proof.
  intros A P. cofix COFIX. intros(*; pfold*). destruct T;constructor;auto.
Qed.

Lemma ForallTraceEq:
  forall {A} (f:A->Prop) T1 T2,
    T1 ~= T2 ->
    ForallTrace f T1 ->
    ForallTrace f T2. 
Proof.
  intros A f. cofix COFIX. intros T1 T2 H H0(*; pfold*).
  destruct H.
  inv H0.
  - constructor. auto.
  - inv H0. constructor. auto. (*right.*) eapply COFIX; eauto.
Qed.

Add Parametric Morphism A (f:A->Prop) : (@ForallTrace A f)
    with signature (@TraceEq A) ==> Basics.impl as forall_mor.
Proof.
  exact (@ForallTraceEq A f).                                                                                   Qed.                            
Inductive Last {A} : TraceOf A -> A -> Prop :=
| LastNow : forall a, Last (finished a) a
| LastLater : forall T a a', Last T a -> Last (notfinished a' T) a
.

Lemma LastUnique :
  forall {A} (a1 a2 : A) T,
    Last T a1 ->
    Last T a2 ->
    a1 = a2.
Proof.
  intros. induction H; inversion H0; auto.
Qed.

Lemma LastInTrace :
  forall A (t:A) (T:TraceOf A),
    Last T t -> InTrace t T.
Proof.
  intros. induction H.
  - constructor.
  - constructor. auto.
Qed.

Lemma LastTraceEq :
  forall {A} (T1 T2: TraceOf A),
    TraceEq T1 T2 ->
    forall a, Last T1 a ->
    Last T2 a.
Proof.
  intros.
  generalize dependent T2.
  induction H0; intros. 
  - inv H. constructor.
  - inv H. constructor.  apply IHLast. auto.
Qed.


Add Parametric Morphism A : (@Last A)
    with signature (@TraceEq A) ==> eq  ==> Basics.impl as last_mor.
Proof.
  exact (@LastTraceEq A). 
Qed.


(* Divide MM1 into MM2 ++ MMO such that MM2 is the longest prefix for which P holds on each element *)
Definition TraceSpan {A} (P : A -> Prop) (T1 T2 : TraceOf A) (TO : option (TraceOf A)) : Prop :=
  T1 = T2^TO /\ ForallTrace P T2 /\
  forall T2', T2' <<== T1 ->
    ForallTrace P T2' ->
    T2' <<== T2.

(* T2 is the longest prefix of T1 for which P holds on each element. *)
Definition LongestPrefix {A} (P : A -> Prop) (T1 T2 : TraceOf A) : Prop :=
  exists TO, TraceSpan P T1 T2 TO.

Inductive SplitInclusive {A} (P:A -> Prop) : TraceOf A -> TraceOf A -> TraceOf A -> Prop :=
| PNowFinished : forall a, P a -> SplitInclusive P (finished a) (finished a) (finished a)
| PNowNotFinished : forall a T, P a -> SplitInclusive P (notfinished a T) (finished a) (notfinished a T)
| PLater : forall a T Tpre Tsuff,
    ~ P a ->
    SplitInclusive P T Tpre Tsuff ->
    SplitInclusive P (notfinished a T) (notfinished a Tpre) Tsuff.

CoFixpoint JoinInclusive {A} (T1 T2 : TraceOf A) : TraceOf A :=
  match T1 with
  | finished a => T2
  | notfinished a T1' => notfinished a (JoinInclusive T1' T2)
  end.

Notation "T1 ^^ T2" := (JoinInclusive T1 T2) (at level 80).

Lemma SplitInclusiveHeadEq :
  forall {A} (P:A->Prop) T1 T2 T3,
    SplitInclusive P T1 T2 T3 ->
    head T1 = head T2.
Proof.
  intros. induction H; auto.
Qed.

Lemma SplitInclusiveIsInclusive :
  forall {A} P (T1 T2 T3 : TraceOf A),
    SplitInclusive P T1 T2 T3 ->
    Last T2 (head T3).
Proof.
  intros. induction H; constructor; auto.
Qed.

Lemma SplitInclusiveHead {A} (p : A -> Prop) (T Tpre Tsuff : TraceOf A) :
  SplitInclusive p T Tpre Tsuff -> head T = head Tpre.
Proof.
  intros H; inversion H; auto.
Qed.

Lemma SplitInclusiveHasLast {A : Type} (p : A -> Prop) :
  forall T Tpre Tsuff, SplitInclusive p T Tpre Tsuff ->
                       exists a, Last Tpre a.
Proof.
  intros T Tpre Tsuff H; induction H.
  - eexists; econstructor.
  - eexists; econstructor.
  - destruct IHSplitInclusive; eexists; econstructor; eauto.
Qed.

Lemma SplitInclusiveProp {A} (p : A -> Prop) :
  forall T Tpre Tsuff, SplitInclusive p T Tpre Tsuff ->
                       p (head Tsuff).
Proof.
  intros. induction H; simpl; auto.
Qed.

Definition PrefixUpTo {A} (p : A -> Prop) (T Tpre : TraceOf A) : Prop :=
  (exists Tsuff, SplitInclusive p T Tpre Tsuff) \/
  ForallTrace (fun m => ~ (p m)) T /\ TraceEq T Tpre.

Lemma PrefixUpToHead {A} (p : A -> Prop) (T Tpre : TraceOf A) :
  PrefixUpTo p T Tpre -> head T = head Tpre.
Proof.
  intros [[Tsuff Hpre] | [? Eq]].
  - eapply SplitInclusiveHead; eauto.
  - inversion Eq; auto.
Qed.

Definition infinite {A} (T : TraceOf A) : Prop :=
  forall a, ~ Last T a.

CoInductive Infinite {A}  : TraceOf A -> Prop :=
| InfI : forall a T,  Infinite T -> Infinite (notfinished a T). 

Lemma Inf_inf: forall {A} (T:TraceOf A), Infinite T -> infinite T. 
Proof.
  intros.
  unfold infinite. 
  intros. intro.
  induction H0. 
  inv H. 
  apply IHLast. 
  inv H. 
  apply H2.
Qed.

Lemma inf_Inf: forall {A} (T:TraceOf A), infinite T -> Infinite T.
Proof.  
  cofix COFIX; intros.
  destruct T. 
  - exfalso. unfold infinite in H.  eapply H. constructor.
  - constructor.  apply COFIX. 
    unfold infinite in *. intros. pose proof (H a0). intro. apply H0. constructor. apply H1. 
Qed.

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

Lemma MapOverJoin {A B} (f : A -> B) :
  forall T T',
    mapTrace f (T ^^ T') ~= (mapTrace f T ^^ mapTrace f T').
Proof.
  cofix COFIX. intros.
  destruct T eqn:E.
  - destruct T'; join_frobber.
    + maptrace_frobber. fold (mapTrace f (finished a)).
      maptrace_frobber. join_frobber. constructor.
    + maptrace_frobber. fold (mapTrace f (notfinished a0 T')).
      join_frobber. maptrace_frobber. constructor. fold (mapTrace f T').
      apply TraceEqRefl.
  - replace (mapTrace f (notfinished a t ^^ T')) with
        (notfinished (f a) (mapTrace f (t ^^ T'))).
    + replace (mapTrace f (notfinished a t) ^^ mapTrace f T') with
          (notfinished (f a) (mapTrace f t ^^ mapTrace f T')).
      * constructor. apply COFIX. 
      * maptrace_frobber. join_frobber. constructor.
    + join_frobber. maptrace_frobber. constructor.
Qed.

Lemma MapLast {A B} (f : A -> B) :
  forall T a,
    Last T a ->
    Last (mapTrace f T) (f a).
Proof.
  intros. induction H.
  - maptrace_frobber. constructor.
  - maptrace_frobber. fold (mapTrace f T).
    constructor. auto.
Qed.

Lemma InfJoin {A} :
  forall (T1 T2:TraceOf A) a,
    Last T1 a ->
    infinite (T1^^T2) ->
    infinite T2.
Proof.
  intros. intro. intro.
  induction H; intros.
  - inv H1.
    + join_frobber. apply (H0 a0). constructor.
    + join_frobber. apply (H0 a0). constructor. auto.
  - join_frobber. apply IHLast. intro. intro.
    apply (H0 a1). constructor. auto.
Qed.
