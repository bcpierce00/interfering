From StackSafety Require Import MachineModule PolicyModule.
From QuickChick Require Import QuickChick.
Require Import Coq.Strings.String. Open Scope string_scope.

Module Type LayoutInfo (M : Machine).
  Import M.
  Module PM := Properties M.
  Export PM.

  Parameter LayoutInfo : Type.
  Parameter defLayoutInfo : LayoutInfo.
  Parameter defStackMap : LayoutInfo -> StackMap.
  Parameter initCtx : Ctx.
  Parameter CodeMap_Impl : Type.
  Parameter CodeMap_fromImpl : CodeMap_Impl -> CodeMap.
End LayoutInfo.

Module Type Gen (M : Machine) (LI : LayoutInfo M).
  Import M.
  Import LI.
  Module PM := Properties M.
  Import PM.
  
  Parameter genVariantOf : nat -> Ctx -> MachineState -> G MachineState.
  Parameter genVariantByList : list Element -> MachineState -> G MachineState.
  
  Parameter genMach : G (MachineState * CodeMap_Impl).
End Gen.

Module Type Printing (M : Machine) (LI : LayoutInfo M).
  Import M.
  Import LI.
  
  Parameter printObsType : Event -> string.
  Instance ShowObsType : Show Event :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Parameter printPC : MachineState -> string.
  
  Parameter printComponent : Element -> MachineState ->
                             CodeMap_Impl -> Ctx -> LayoutInfo -> string.

  Parameter printMachine : MachineState -> CodeMap_Impl -> Ctx -> string.

  Instance ShowM : Show (MachineState * CodeMap_Impl) :=
    {| show := fun '(m,cm) => printMachine m cm initCtx |}.
End Printing.

Module Type TestProps (M : Machine) (LI : LayoutInfo M).
  Parameter prop_integrity : Checker.
  Parameter prop_confidentiality : Checker.
  Parameter prop_laziestIntegrity : Checker.
  Parameter prop_laziestIntegrity' : Checker. (* NOTE Temporary addition, replace old one later *)
  Parameter prop_lazyConfidentiality : Checker.
End TestProps.

