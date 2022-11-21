From StackSafety Require Import MachineModule.

Module Type Policy(M:Machine).
  Import M.

  Parameter PolicyState : Type.

  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.

  Parameter pstep : MPState -> option PolicyState.

  Parameter mpstep : MPState -> option (MPState * list Operation * Observation).

  Parameter mpstepCompat :
    forall m p t o m' p',
      mpstep (m,p) = Some (m',p',t,o) ->
      step m = (m',t,o).

  Parameter WFInitMPState : MPState -> Prop.

End Policy.
