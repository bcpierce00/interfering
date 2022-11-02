From StackSafety Require Import MachineModule.

Module Type MapMaker (M : Machine).
  Import M.
  Parameter cdm : CodeMap.
  Parameter sm : StackMap.
  Parameter defaultStack : StackID.
End MapMaker.
