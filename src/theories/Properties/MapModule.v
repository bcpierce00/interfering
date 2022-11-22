From StackSafety Require Import MachineModule.

Module Type MapMaker (M : Machine).
  Import M.
  (* TODO: The following parameters are left over from the previous version of
     the formalization. They are not present in [RISCVMachine] but they remain
     vestigially in [RISCVObs]. Both need to be replaced. *)
  (* Parameter cdm : CodeMap. *)
  (* Parameter sm : StackMap. *)
  (* Parameter defaultStack : StackID. *)
End MapMaker.
