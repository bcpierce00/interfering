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
| EqFin : forall m, TraceEq (finished m) (finished m)
| EqCons : forall m mm1 mm2, TraceEq mm1 mm2 ->
                             TraceEq (notfinished m mm1) (notfinished m mm2).

Lemma TraceEqRefl: forall {A} (M: TraceOf A),
    TraceEq M M.
Proof.
  cofix COFIX.
  intros. 
  destruct M. 
  - constructor.
  - constructor; apply COFIX.     
Qed.

Lemma TraceEqTrans : forall {A} (M1 M2 M3: TraceOf A),
    TraceEq M1 M2 ->
    TraceEq M2 M3 ->
    TraceEq M1 M3. 
Proof.
  cofix COFIX.
  intros.
  inversion H; subst.
  - inversion H0; subst. 
    constructor. 
  - inversion H0; subst. 
    constructor. eapply COFIX; eauto. 
Qed.

Lemma TraceEqSym : forall {A} (M1 M2: TraceOf A),
    TraceEq M1 M2 ->
    TraceEq M2 M1.
Proof.
  cofix COFIX.
  intros.
  inversion H; subst.
  - constructor.
  - constructor. apply COFIX; auto. 
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

(* TracePrefix MM1 MM2 says MM2 is a prefix of MM1. *)
Definition TracePrefix {A} (T1 T2: TraceOf A): Prop :=
  exists TO,
    T1 = T2^TO.

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

(* TODO: Rename to Last *)
Inductive IsEnd {A} : TraceOf A -> A -> Prop :=
| IsEndNow : forall a, IsEnd (finished a) a
| IsEndLater : forall T a a', IsEnd T a -> IsEnd (notfinished a' T) a
.

Inductive SplitInclusive {A} (P:A -> Prop) : TraceOf A -> TraceOf A -> TraceOf A -> Prop :=
| PNowFinished : forall a, P a -> SplitInclusive P (finished a) (finished a) (finished a)
| PNowNotFinished : forall a T, P a -> SplitInclusive P (notfinished a T) (finished a) (notfinished a T)
| PLater : forall a T Tpre Tsuff,
    ~ P a ->
    SplitInclusive P T Tpre Tsuff ->
    SplitInclusive P (notfinished a T) (notfinished a Tpre) Tsuff.

Lemma SplitInclusiveIsInclusive : forall {A} P (T1 T2 T3 : TraceOf A),
    SplitInclusive P T1 T2 T3 ->
    InTrace (head T3) T2.
Proof.
  intros. induction H; constructor; auto.
Qed.

Lemma SplitInclusiveHead {A} (p : A -> Prop) (T Tpre Tsuff : TraceOf A) :
  SplitInclusive p T Tpre Tsuff -> head T = head Tpre.
Proof.
  intros H; inversion H; auto.
Qed.

Lemma SplitInclusiveHasEnd {A : Type} (p : A -> Prop) :
  forall T Tpre Tsuff, SplitInclusive p T Tpre Tsuff ->
                       exists a, IsEnd Tpre a.
Proof.
  intros T Tpre Tsuff H; induction H.
  - eexists; econstructor.
  - eexists; econstructor.
  - destruct IHSplitInclusive; eexists; econstructor; eauto.
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

Lemma IsEndInTrace :
  forall A (t:A) (T:TraceOf A),
    IsEnd T t -> InTrace t T.
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

Axiom TraceAppNone :
  forall A (T : TraceOf A),
    T = T^None.

Lemma TracePrefix_refl :
  forall A (T:TraceOf A),
    T <<== T.
Proof.
  intros. exists None. apply TraceAppNone.
Qed.

Axiom TraceAppFinished :
  forall A (a:A) (T:TraceOf A),
    finished a ^ Some T = notfinished a T.

Axiom IsEndAppFinish :
  forall A (T:TraceOf A) (a:A),
    IsEnd (T^Some (finished a)) a.

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

