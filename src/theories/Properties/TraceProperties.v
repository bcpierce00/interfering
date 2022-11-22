Require Import List.
Import ListNotations.
Require Import Bool.

From StackSafety Require Import Trace MachineModule ObsTrace PolicyModule CtxModule MPC.

Module TraceProps (M : Machine) (P : Policy M) (C : Ctx M).
  Import M.
  Import P.
  Import C.
  Module MPCimpl := MPC M P C.
  Import MPCimpl.
  Module Obs := ObsTrace M.
  Import Obs.
  
  Definition variantOf (K : Element -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> proj m k = proj n k.

  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (proj m k <> proj m' k \/ proj n k <> proj n' k) ->
      proj m' k = proj n' k.

  Inductive Lockstep : MPCTrace -> MPCTrace -> Prop :=
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
             (K : Element -> Prop)
             (P : MPCState -> Prop)
             (M : MPCTrace) : Prop :=
    forall m p c n N,
      head M = (m,p,c) ->
      variantOf K m n ->
      MPCTraceToWhen P (n,p,c) N ->
      Lockstep M N.

  Definition StepIntegrity (K : Element -> Prop) (mpc:MPCState) : Prop :=
    forall mpc' t o k,
    mpcstep mpc = Some (mpc',t,o) ->
    K k ->
    proj (mstate mpc) k = proj (mstate mpc') k.

  Definition TraceIntegrityObs
             (K : Element -> Prop)
             (M : MPCTrace) : Prop :=
    forall m p c,
      Last M (m,p,c) ->
      let K' := fun k => K k /\ proj (mstate (head M)) k <> proj (mstate (m,p,c)) k in
      let P := fun _ => False in
      TraceConfidentialityStep K' P (MPCTraceOf (m,p,c)).

  Definition TraceConfidentialityObs
             (K : Element -> Prop)
             (P : MPCState -> Prop)
             (M : MPCTrace) : Prop :=
    forall m p c n N Om On, 
      head M = (m,p,c) ->
      variantOf K m n ->
      MPCTraceToWhen P (n,p,c) N ->
      ObsOfMPC M Om ->
      ObsOfMPC N On ->
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
          FullObsTrace (mend,pend,cend) Om' ->
          FullObsTrace (n',pend,cend) On' ->
          Om' ~=_O On').

End TraceProps.
