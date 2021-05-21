From StackSafety Require Import MachineModule PolicyModule TestCtxModule LayoutInfoModule.

From QuickChick Require Import QuickChick.

Module TestMPC (M : Machine) (P : Policy M) (LI : LayoutInfo M) (C : TestCtx M LI).
  Import M.
  Import P.
  Import C.
  Import LI.
  
  Definition MPCState : Type := MachineState * PolicyState * CtxState.
  Definition mstate : MPCState -> MachineState := fun '(m,p,cs) => m.
  Definition pstate : MPCState -> PolicyState := fun '(m,p,cs) => p.
  Definition cstate : MPCState -> CtxState := fun '(m,p,cs) => cs.
  Definition mpcstep (mpc:MPCState) (cm : CodeMap_Impl) : option (MPCState * Observation) :=
    option_map
      (fun '(m,p,o) => (m,p,CtxStateUpdate (mstate mpc) cm (cstate mpc),o))
      (mpstep (mstate mpc,pstate mpc)).
End TestMPC.
