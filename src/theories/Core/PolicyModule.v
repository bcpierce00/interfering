From StackSafety Require Import MachineModule.

Import ZArith.
  
Module Type TagPolicy (M : Machine).
  Import M.
  
  Parameter Tag : Type.
  
  Parameter PolicyState : Type.

  Parameter projt : PolicyState -> Element -> Tag.
  Parameter jorpt : PolicyState -> Element -> Tag -> PolicyState.
  
  Definition MPState : Type := MachineState * PolicyState.

  Parameter pstep : MachineState -> PolicyState -> option PolicyState.

  Definition mpstep (mp : MPState) : (MPState * list Operation * Observation) :=
    let '(m,p) := mp in
    match pstep m p with
    | Some p' =>
        let '(m',ops,o) := step m in
        (m',p',ops,o)
    | None => (m,p,nil,Tau)
    end.

  Parameter tagify_head : Z -> list (instr * list Operation) -> list (instr * Tag * list Operation).

End TagPolicy.
