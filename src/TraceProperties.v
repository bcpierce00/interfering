Require Import List.
Import ListNotations.
Require Import Bool.

From StackSafety Require Import Trace MachineImpl ObsTrace.

Section WITH_CONTEXT.

  Variable context : Type.
  Variable updateC : MachineState -> context -> context.

  Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> proj m k = proj n k.

  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (proj m k <> proj m' k \/ proj n k <> proj n' k) ->
      proj m' k = proj n' k.

  Inductive Lockstep : @MPCTrace context -> @MPCTrace context -> Prop :=
  | bothDone : forall m p c n,
      Lockstep (finished (m,p,c)) (finished (n,p,c))
  | bothStep : forall m p c m' n n' M N,
      mstate (head M) = m' ->
      mstate (head N) = n' ->
      sameDifference m m' n n' ->
      Lockstep M N ->
      Lockstep (notfinished (m,p,c) M) (notfinished (n,p,c) N)
  .

  Definition TraceConfidentialityStep
             (K : Component -> Prop)
             (P : MPCState -> Prop)
             (M : @MPCTrace context) : Prop :=
    forall m p c n N,
      head M = (m,p,c) ->
      variantOf K m n ->
      MPCTraceToWhen updateC P (n,p,c) N ->
      Lockstep M N
  .

  Definition StepIntegrity (K : Component -> Prop) (mpc:@MPCState context) : Prop :=
    forall mpc' o k,
    mpcstep updateC mpc = Some (mpc',o) ->
    K k ->
    proj (mstate mpc) k = proj (mstate mpc') k.

  Definition TraceIntegrityLazy
             (K : Component -> Prop)
             (M : @MPCTrace context) : Prop :=
    forall m p c,
      Last M (m,p,c) ->
      let K' := fun k => K k /\ proj (mstate (head M)) k <> proj (mstate (m,p,c)) k in
      let P := fun _ => False in
      TraceConfidentialityStep K' P (MPCTraceOf updateC (m,p,c)).

  Definition TraceConfidentialityLazy
             (K : Component -> Prop)
             (P : MPCState -> Prop)
             (M : @MPCTrace context) : Prop :=
    forall m p c n N Om On, 
      head M = (m,p,c) ->
      variantOf K m n ->
      MPCTraceToWhen updateC P (n,p,c) N ->
      ObsOfMPC updateC M Om ->
      ObsOfMPC updateC N On ->
      Om ~=_O On /\
      ((exists mpcend, Last M mpcend /\ P mpcend) <->
       (exists npcend, Last N npcend /\ P npcend)) /\
      (forall mend nend pend cend n' Om' On',
          Last M (mend,pend,cend) ->
          Last N (nend,pend,cend) ->
          P (mend,pend,cend) ->
          P (nend,pend,cend) ->
          let K' := fun k => proj mend k <> proj nend k in
          variantOf K' mend n' ->
          FullObsTrace updateC (mend,pend,cend) Om' ->
          FullObsTrace updateC (n',pend,cend) On' ->
          Om' ~=_O On').

End WITH_CONTEXT.

Arguments StepIntegrity {_} _ _.
Arguments TraceConfidentialityStep {_} _ _ _ _.
Arguments TraceIntegrityLazy {_} _ _.
Arguments TraceConfidentialityLazy {_} _ _ _ _.
