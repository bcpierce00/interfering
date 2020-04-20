Section foo.

(* TODO: Make all this match the terminology in the .tex -- e.g., a
   Contour should correspond to a MachineState, not to a Trace,
   etc. *)

Variable MachineState : Type.
Variable step : MachineState -> option MachineState.

CoInductive Trace : Type :=
  finished : MachineState -> Trace
| notfinished : MachineState -> Trace -> Trace.

Definition fst (MM : Trace) : MachineState :=
  match MM with
  | finished M => M
  | notfinished M _ => M
  end.

CoFixpoint traceOf (M : MachineState) : Trace :=
  match step M with
  | None => finished M
  | Some M' => notfinished M (traceOf M')
  end.


Variable Contour : Type.
Variable StackIntegrity : Trace -> Contour -> Prop.
Variable StackConfidentiality : Trace -> Trace -> Contour -> Prop.
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