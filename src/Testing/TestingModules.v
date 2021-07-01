From StackSafety Require Import MachineModule PolicyModule.
From QuickChick Require Import QuickChick.
Require Import Coq.Strings.String. Open Scope string_scope.

Module Type LayoutInfo (M : Machine).
  Import M.

  Parameter LayoutInfo : Type.
  Parameter defLayoutInfo : LayoutInfo.
  Parameter defStackMap : LayoutInfo -> StackMap.
  Parameter CodeMap_Impl : Type.
  Parameter CodeMap_fromImpl : CodeMap_Impl -> CodeMap.
End LayoutInfo.

Module Type TestCtx (M:Machine) (LI:LayoutInfo M).
  Import M.
  Import LI.

  Parameter CtxState : Type.
  Parameter initCtx : LayoutInfo -> CtxState.
  Parameter CtxStateUpdate : MachineState -> CodeMap_Impl -> CtxState -> CtxState.

  Parameter interestingComponent : CtxState -> CtxState -> Component -> bool.
  Parameter integrityComponent : CtxState -> Component -> bool.
  Parameter depthOf : CtxState -> nat.
End TestCtx.

Module TestMPC (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Export M.
  Export P.
  Export LI.
  Export C.
  
  Definition MPCState : Type := MachineState * PolicyState * CtxState.
  Definition mstate : MPCState -> MachineState := fun '(m,p,cs) => m.
  Definition pstate : MPCState -> PolicyState := fun '(m,p,cs) => p.
  Definition cstate : MPCState -> CtxState := fun '(m,p,cs) => cs.
  Definition mpcstep (mpc:MPCState) (cm : CodeMap_Impl) : option (MPCState * Observation) :=
    option_map
      (fun '(m,p,o) => (m,p,CtxStateUpdate (mstate mpc) cm (cstate mpc),o))
      (mpstep (mstate mpc,pstate mpc)).
End TestMPC.

Module Type Gen (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Module MPC := TestMPC M P LI C.
  Import MPC.

  Parameter genVariantOf : nat -> CtxState -> MachineState -> G MachineState.
  Parameter genVariantByList : list Component -> MachineState -> G MachineState.
  
  Parameter genMach : G (MachineState * PolicyState * CodeMap_Impl).
End Gen.

Module Type Printing (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Module MPC := TestMPC M P LI C.
  Import MPC.

  Parameter printObsType : ObsType -> string.
  Instance ShowObsType : Show ObsType :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Parameter printPC : MachineState -> PolicyState -> string.
  
  Parameter printComponent : Component -> MachineState -> PolicyState -> 
                             CodeMap_Impl -> CtxState -> LayoutInfo -> string.

  Parameter printMachine : MachineState -> PolicyState -> CodeMap_Impl -> CtxState -> string.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
    {| show := fun '(m,p,cm) => printMachine m p cm (initCtx defLayoutInfo) |}.
End Printing.

Module Type TestProps (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Parameter prop_integrity : Checker.
  Parameter prop_confidentiality : Checker.
  Parameter prop_laziestIntegrity : Checker.
End TestProps.

