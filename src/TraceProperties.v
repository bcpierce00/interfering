Require Import List.
Import ListNotations.
Require Import Bool.

From StackSafety Require Import Trace MachineImpl ObsTrace.

Section WITH_CONTEXT.

  Variable context : Type.
  Variable updateC : MachineState -> context -> context.

  (* Not really using this one.*)
(*  Definition TraceIntegrityEager (K : Component -> Prop) (MPC:MPCTrace) : Prop :=
    forall k (mcp':@MPCState context),
      K k->
      Last MPC mcp' ->
      proj (mstate (head MPC)) k = proj (mstate mcp') k.*)
  
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
    forall m p c n N,
      head M = (m,p,c) ->
      variantOf K m n ->
      MPCTraceToWhen updateC P (n,p,c) N ->
      (exists mend nend pend cend,
          Last M (mend,pend,cend) /\
          Last N (nend,pend,cend) /\
          P (mend,pend,cend) /\
          P (nend,pend,cend) /\
          let K := fun k => mend <> nend in
          TraceConfidentialityStep K P (MPCTraceOf updateC (mend,pend,cend))) \/
      (exists mpcend npcend,
          Last M mpcend /\
          Last N npcend /\
          ~ P mpcend /\
          ~ P npcend) \/
      (Infinite M /\ Infinite N).

(*Definition TraceConfidentialityEager
             (K : Component -> Prop)
             (P: MPCState -> Prop)
             (MPC:@MPCTrace context) : Prop :=
    forall MPC m c p n N Om On,
      head MPC = (m,c,p) ->
      variantOf K m n ->
      MPCTraceToWhen updateC P (n,c,p) N ->
      ObsOfMPC updateC MPC Om ->
      ObsOfMPC updateC N On ->

      Om ~=_O On /\

      ((exists mpcend npcend,
          Last MPC mpcend /\
          Last N npcend /\
          P mpcend /\
          P npcend /\
          sameDifference m (mstate mpcend) n (mstate npcend)) \/
      (Infinite MPC /\ Infinite N) \/
      (exists mpcend npcend,
          Last MPC mpcend /\
          Last N npcend /\
          ~ P mpcend /\
          ~ P npcend)). *)
      
End WITH_CONTEXT.

Arguments StepIntegrity {_} _ _.
Arguments TraceConfidentialityStep {_} _ _ _ _.
Arguments TraceIntegrityLazy {_} _ _.
Arguments TraceConfidentialityLazy {_} _ _ _ _.

