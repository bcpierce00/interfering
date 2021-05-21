From StackSafety Require Import MachineModule PolicyModule TestCtxModule LayoutInfoModule.
Require Import Coq.Strings.String. Open Scope string_scope.

From QuickChick Require Import QuickChick.

Module Type Printing (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Import M.
  Import P.
  Import C.
  Import LI.

  Parameter printObsType : ObsType -> string.
  Instance ShowObsType : Show ObsType :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Parameter printComponent : Component -> MachineState -> PolicyState -> 
                             CodeMap_Impl -> CtxState -> LayoutInfo -> string.

  Parameter printMachine : MachineState -> PolicyState -> CodeMap_Impl -> CtxState -> string.

  Parameter walk : list Component -> CodeMap_Impl -> MachineState -> PolicyState -> CtxState ->
                   MachineState -> PolicyState -> CtxState -> list (ObsType -> string) ->
                   (ObsType -> Checker) -> Checker.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
    {| show := fun '(m,p,cm) => "" (*printMachine m p cm (initC (defstackmap defLayoutInfo) m) *) |}.

End Printing.
