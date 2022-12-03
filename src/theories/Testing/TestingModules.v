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

Module Type Gen (M : Machine) (P : Policy M) (LI : LayoutInfo M).
  Import M.
  Import P.
  Import LI.
  Module PM := Properties M.
  Import PM.
  
  Parameter genVariantOf : nat -> Ctx -> MachineState -> G MachineState.
  Parameter genVariantByList : list Element -> MachineState -> G MachineState.
  
  Parameter genMach : G (MachineState * PolicyState * CodeMap_Impl).
End Gen.

Module Type Printing (M : Machine) (P : Policy M) (LI : LayoutInfo M).
  Import M.
  Import P.
  Import LI.

  Parameter printObsType : Event -> string.
  Instance ShowObsType : Show Event :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Parameter printPC : MachineState -> PolicyState -> string.
  
  Parameter printComponent : Element -> MachineState -> PolicyState ->
                             CodeMap_Impl -> Ctx -> LayoutInfo -> string.

  Parameter printMachine : MachineState -> PolicyState -> CodeMap_Impl -> Ctx -> string.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl) :=
    {| show := fun '(m,p,cm) => printMachine m p cm initCtx |}.
End Printing.

Module Type TestProps (M : Machine) (P : Policy M) (LI : LayoutInfo M).
  Parameter prop_integrity : Checker.
  Parameter prop_confidentiality : Checker.
  Parameter prop_laziestIntegrity : Checker.
  Parameter prop_laziestIntegrity' : Checker. (* NOTE Temporary addition, replace old one later *)
End TestProps.

