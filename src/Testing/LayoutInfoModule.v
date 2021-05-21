From StackSafety Require Import MachineModule.

Module Type LayoutInfo (M : Machine).
  Import M.
  Parameter LayoutInfo : Type.
  Parameter defLayoutInfo : LayoutInfo.
  Parameter defStackMap : LayoutInfo -> StackMap.
  Parameter CodeMap_Impl : Type.
  Parameter CodeMap_fromImpl : CodeMap_Impl -> CodeMap.
End LayoutInfo.
