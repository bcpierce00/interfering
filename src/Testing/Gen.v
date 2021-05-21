From StackSafety Require Import MachineModule PolicyModule TestCtxModule LayoutInfoModule.

From QuickChick Require Import QuickChick.

Module Type Gen (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Import M.
  Import P.
  Import C.
  Import LI.

  Parameter genVariantOf : nat -> CtxState -> MachineState -> G MachineState.
  
  Parameter genMach : G (MachineState * PolicyState * CodeMap_Impl).
End Gen.
