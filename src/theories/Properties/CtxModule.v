From StackSafety Require Import MachineModule.

Module Type Ctx (M:Machine).
  Import M.

  Parameter CtxState : Type.
  Parameter CtxStateUpdate : MachineState -> CtxState -> CtxState.
  Parameter initCtx : MachineState -> CtxState.
End Ctx.
