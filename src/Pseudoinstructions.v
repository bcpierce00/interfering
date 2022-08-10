Require Import ZArith.
Require Import List. Import ListNotations.

From QuickChick Require Import QuickChick.
Import QcNotation.

Definition fid : Type := nat.

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

Parameter gen_fun : list pfun -> G nat.

Definition gen_pi (fs : list pfun) : G pseudoinstr :=
  freq
    [(1, (liftGen I) gen_i);
     (1, ret Return);
     (1, (liftGen Call) (gen_fun fs))
    ].

Definition PC : Type := nat * nat.

Definition fetch (fs : list pfun) (pc : PC) : option pseudoinstr :=
  match nth_error fs (fst pc) with
  | Some f => nth_error (proj1_sig f) (snd pc)
  | None => None
  end.

Parameter mstate : Type.

Definition genstate : Type := mstate * PC * list pfun.

Parameter genstep : genstate -> genstate.

(*Fixpoint gen_prog_funs (gas : nat) (fs : list pfun) ( *)
