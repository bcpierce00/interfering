From StackSafety Require Import Trace Machine.

Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.Minimal.
Require Import riscv.Platform.MinimalLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Z.HexNotation.
Require coqutil.Map.SortedList.

Require Import Lia.

Module MachineImpl : MachineSpec.

  Definition Word := MachineInt.
(* Parameter Word *)

Definition wlt : Word -> Word -> bool := Z.ltb.
(*  Parameter wlt : Word -> Word -> bool. *)

Definition weq : Word -> Word -> bool := Z.eqb.
(* Parameter weq : Word -> Word -> bool. *)

Definition WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2} := Z.eq_dec.

Lemma weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.
  apply Z.eqb_eq.
Qed.

Lemma not_weq_implies_neq :
    forall w1 w2,
      weq w1 w2 = false -> w1 <> w2.
Proof. 
  intros w1 w2 HEqb HEq. unfold weq in *.
  apply Z.eqb_eq in HEq.
  rewrite HEq in HEqb.
  congruence.
Qed.

Definition wle (w1 w2: Word) : bool :=
  orb (wlt w1 w2) (weq w1 w2).

(*
Parameter wplus : Word -> nat -> Word.
Parameter wminus : Word -> nat -> Word.
*)  
Definition wplus (w : Word) (n : nat) : Word :=
  w + Z.of_nat n.

Lemma wplus_neq : forall w (n : nat),
    (n > O)%nat -> w <> wplus w n.
Proof.
  intros w n H Contra.
  unfold wplus in *.
  lia.
Qed.

Definition wminus (w : Word) (n : nat) : Word :=
  w - Z.of_nat n.

Definition Addr : Type := Word.

Definition Register : Type := Word.


End MachineImpl.
