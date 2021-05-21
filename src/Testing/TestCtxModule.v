From StackSafety Require Import MachineModule LayoutInfoModule.

Module Type TestCtx (M:Machine) (LI:LayoutInfo M).
  Import M.
  Import LI.

  Parameter CtxState : Type.
  Parameter initCtx : LayoutInfo -> CtxState.
  Parameter CtxStateUpdate : MachineState -> CodeMap_Impl -> CtxState -> CtxState.

  Parameter interestingComponent : CtxState -> CtxState -> Component -> bool.
  Parameter depthOf : CtxState -> nat.

  (*Parameter LayoutInfo : Type.
  Parameter defStackMap : LayoutInfo -> StackMap.*)
(*  Parameter CodeMap_Impl : Type.

  Parameter CodeMap_fromImpl : CodeMap_Impl -> CodeMap.*)
End TestCtx.
