Require Import ZArith.
Require Import List. Import ListNotations.

From QuickChick Require Import QuickChick.

Definition fid : Type := positive.

Parameter instr : Type.

Inductive pseudoinstr :=
| Call (f:fid)
| Return
| Enter
| I (i:instr)
.

Parameter pi_to_is :
  pseudoinstr -> list instr.

Parameter pi_to_is_consistent :
  forall i,
    pi_to_is (I i) = [i].

Definition pfun : Type := {pis: list pseudoinstr | exists pis', pis = Enter::pis'}.

Parameter gen_i : G instr.
