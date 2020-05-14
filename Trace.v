Require Export Setoid.

Ltac inv H := inversion H; subst; clear H.

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

CoInductive ForallTrace {A:Type} (P:A -> Prop) : TraceOf A -> Prop :=
| Forall_finished : forall a, P a -> ForallTrace P (finished a)
| Forall_notfinished : forall a T', P a -> ForallTrace P T' -> ForallTrace P (notfinished a T')
.

CoInductive TraceEq {A} : TraceOf A -> TraceOf A -> Prop :=
| EqFin : forall a, TraceEq (finished a) (finished a)
| EqCons : forall a T1 T2, TraceEq T1 T2 ->
                             TraceEq (notfinished a T1) (notfinished a T2).


Notation "T1 ~= T2" := (TraceEq T1 T2) (at level 80). 

Lemma TraceEqRefl: forall {A} (T: TraceOf A),
    TraceEq T T.
Proof.
  cofix COFIX.
  intros.
  destruct T.
  - constructor.
  - constructor; apply COFIX.     
Qed.

Lemma TraceEqTrans : forall {A} (T1 T2 T3: TraceOf A),
    TraceEq T1 T2 ->
    TraceEq T2 T3 ->
    TraceEq T1 T3. 
Proof.
  cofix COFIX.
  intros.
  inversion H; subst.
  - inversion H0; subst. 
    constructor. 
  - inversion H0; subst. 
    constructor. eapply COFIX; eauto. 
Qed.

Lemma TraceEqSym : forall {A} (T1 T2: TraceOf A),
    TraceEq T1 T2 ->
    TraceEq T2 T1.
Proof.
  cofix COFIX.
  intros.
  inversion H; subst.
  - constructor.
  - constructor. apply COFIX; auto. 
Qed.

Add Parametric Relation A : (TraceOf A) (@TraceEq A)
    reflexivity proved by (TraceEqRefl (A := A))
    symmetry proved by (TraceEqSym (A := A))                            
    transitivity proved by (TraceEqTrans (A := A))
as TraceEq_rel                             
.                                        

Lemma TraceEqHead : forall {A} (T1 T2: TraceOf A), TraceEq T1 T2 -> head T1 = head T2. 
Proof.
  destruct 1; auto. 
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
                                
Lemma TraceAppEq {A} : 
      forall (T1 T1' : TraceOf A) ,
        TraceEq T1 T1' ->
       forall (TO2 TO2': option(TraceOf A)),
        OpTraceEq TO2 TO2' ->
        TraceEq (T1 ^ TO2) (T1' ^ TO2'). 
Proof.
  cofix COFIX.
  intros. 
  inv H.
  - rewrite idTrace_eq. rewrite (idTrace_eq (finished a ^ TO2)). simpl. 
    destruct TO2, TO2'; simpl in H0.
    * constructor. auto. 
    * inv H0. 
    * inv H0. 
    * constructor. 
  - rewrite idTrace_eq. rewrite (idTrace_eq (notfinished a T0 ^ TO2)). simpl. 
    constructor. apply COFIX; auto. 
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

(* TracePrefix T1 T2 says T2 is a prefix of T1. *)
Definition TracePrefix {A} (T1 T2: TraceOf A): Prop :=
  exists TO,
    TraceEq T1 (T2^TO).

Notation "T2 <<== T1" := (TracePrefix T1 T2) (at level 80).

(* Divide MM1 into MM2 ++ MMO such that MM2 is the longest prefix for which P holds on each element *)
Definition TraceSpan {A} (P : A -> Prop) (T1 T2 : TraceOf A) (TO : option (TraceOf A)) : Prop :=
  T1 = T2^TO /\ ForallTrace P T2 /\
  forall T2', T2' <<== T1 ->
    ForallTrace P T2' ->
    T2' <<== T2.

(* T2 is the longest prefix of T1 for which P holds on each element. *)
Definition LongestPrefix {A} (P : A -> Prop) (T1 T2 : TraceOf A) : Prop :=
  exists TO, TraceSpan P T1 T2 TO.

Inductive Last {A} : TraceOf A -> A -> Prop :=
| LastNow : forall a, Last (finished a) a
| LastLater : forall T a a', Last T a -> Last (notfinished a' T) a
.

Inductive SplitInclusive {A} (P:A -> Prop) : TraceOf A -> TraceOf A -> TraceOf A -> Prop :=
| PNowFinished : forall a, P a -> SplitInclusive P (finished a) (finished a) (finished a)
| PNowNotFinished : forall a T, P a -> SplitInclusive P (notfinished a T) (finished a) (notfinished a T)
| PLater : forall a T Tpre Tsuff,
    ~ P a ->
    SplitInclusive P T Tpre Tsuff ->
    SplitInclusive P (notfinished a T) (notfinished a Tpre) Tsuff.

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

(************************
 Trace Lemmas and axioms 
*************************)

Lemma LastInTrace :
  forall A (t:A) (T:TraceOf A),
    Last T t -> InTrace t T.
Proof.
  intros. induction H.
  - constructor.
  - constructor. auto.
Qed.

Lemma ForallInTrace :
  forall A (f:A->Prop) T t,
    InTrace t T ->
    ForallTrace f T ->
    f t.
Proof.
  intros. induction H; inversion H0; auto.
Qed.

Lemma ForallTraceTautology :
  forall A (P:A->Prop) (T:TraceOf A),
    (forall a, P a) -> ForallTrace P T.
Proof.
  cofix COFIX. intros. destruct T;constructor;auto.
  Guarded.
Qed.

Lemma SplitInclusivePHead :
  forall {A} P (T1 T2 T3 : TraceOf A),
    SplitInclusive P T1 T2 T3 ->
    P (head T3).
Proof.
  intros. induction H; auto.
Qed.

Lemma LastUnique :
  forall {A} (a1 a2 : A) T,
    Last T a1 ->
    Last T a2 ->
    a1 = a2.
Proof.
  intros. induction H; inversion H0; auto.
Qed.

Lemma TraceAppNone :
  forall A (T : TraceOf A),
    TraceEq T (T^None).
Proof.
  cofix COFIX. intros. rewrite idTrace_eq. destruct T.
  - simpl. constructor.
  - simpl. constructor. apply COFIX. Guarded.
Qed.
  
Lemma TracePrefix_refl :
  forall A (T:TraceOf A),
    T <<== T.
Proof.
  intros. exists None. apply TraceAppNone.
Qed.


Lemma LastTraceEq :
  forall {A} (a:A) T1 T2,
    Last T1 a ->
    TraceEq T1 T2 ->
    Last T2 a.
Proof.
  intros. revert T2 H0.  induction H; intros. 
  - inv H0. constructor.
  - inv H0. constructor.  apply IHLast. auto.
Qed.

(*Axiom TraceAppFinished :
  forall A (a:A) (T:TraceOf A),
    finished a ^ Some T = notfinished a T.

Axiom ForallTraceApp :
  forall A f (T1 T2 : TraceOf A),
    ForallTrace f T1 ->
    ForallTrace f T2 ->
    ForallTrace f (T1^Some T2).

Axiom TraceAppAssoc :
  forall A (T1 T2 : TraceOf A) TO,
    T1 ^ Some (T2 ^ TO) = (T1 ^ Some T2) ^ TO.

Axiom ForallImplication :
  forall A (P Q: A -> Prop) (T:TraceOf A),
    (forall a, P a -> Q a) ->
    ForallTrace P T ->
    ForallTrace Q T.

Axiom SpanRemainderNotProp :
  forall A P (T T' T'': TraceOf A),
    TraceSpan P T T' (Some T'') ->
    ~ (P (head T'')).

*)
