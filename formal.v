Section foo.

Variable MachineState : Type.
Variable Trace : Type.
Variable Contour : Type.
Variable StackIntegrity : Trace -> Contour -> Prop.
Variable fst : Trace -> MachineState.
Variable StackConfidentiality : Trace -> Trace -> Contour -> Prop.
Variable traceOf : MachineState -> Trace.
Variable subtrace : Trace -> Trace -> Contour -> Prop.
Variable variantOf : MachineState -> MachineState -> Contour -> Prop.

CoInductive StackSafety : Trace -> Contour -> Prop :=
  ss : forall (MM : Trace) (C : Contour),
       (StackIntegrity MM C) *
       (forall N, variantOf N (fst MM) C ->
                  StackConfidentiality MM (traceOf N) C) *
       (forall Mcallee C',
           subtrace MM Mcallee C' -> StackSafety Mcallee C')
       ->
       StackSafety MM C.

End foo.