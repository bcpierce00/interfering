Require Import List.
Import ListNotations.
Require Import Bool.

From StackSafety Require Import Trace Machine ObsTrace.


  Section WITH_CONTEXT.

  Variable context : Type.
  Variable updateC : MachineState -> context -> context.

  Definition TraceIntegrityEager (K : Component -> Prop) (MPC:MPCTrace) : Prop :=
    forall k (mcp':@MPCState context),
      K k->
      Last MPC mcp' ->
      proj (mstate (head MPC)) k = proj (mstate mcp') k.
  
  Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> proj m k = proj n k.

  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (proj m k <> proj m' k \/ proj n k <> proj n' k) ->
      proj m' k = proj n' k.
  
  Definition TraceConfidentialityEager
             (K : Component -> Prop)
             (P: MPCState -> Prop)
             (MPC:@MPCTrace context) : Prop :=
    forall MPC m c p n N Om On,
      head MPC = (m,c,p) ->
      variantOf K m n ->
      MPCTraceToWhen updateC P (n,c,p) N ->
      ObsOfMPC updateC MPC Om ->
      ObsOfMPC updateC N On ->
      (* Case 1 *)
      (forall mpcend,
          Last MPC mpcend ->
          ~ P mpcend ->
          exists npcend,
            Last N npcend /\
            Om ~=_O On /\
            sameDifference m (mstate mpcend) n (mstate npcend))
    /\ (* Case 2 *)
    (Infinite MPC ->
     Om ~=_O On)
    /\ (* Case 3 *)
    (forall mpcend,
        Last MPC mpcend ->
        P mpcend ->
        Om <=_O On).

End WITH_CONTEXT.

Arguments TraceIntegrityEager {_} _ _.
Arguments TraceConfidentialityEager {_} _ _ _ _.

