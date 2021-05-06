Require Import Coq.Lists.List.
Import List.ListNotations.

From StackSafety Require Import Trace MachineModule MachineImpl.

Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.

Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.Minimal.
Require Import riscv.Platform.MinimalLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Z.HexNotation.
Require coqutil.Map.SortedList.

Require Import Lia.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Module EagerInitGlobal <: Policy RISCV.
  Import RISCV.

(* TODO: More interesting state/abstract *)
Inductive Tag : Type :=
| Tcall
| Tglobal
| Th1
| Th2
| Tinit
| Tinstr
| Tpc (n : nat)
| Tr1
| Tr2
| Tr3
| Tsp
| Tstack (n : nat)
.

Definition tag_eqb (t1 t2 :  Tag) : bool :=
  match t1, t2 with
  | Tcall, Tcall
  | Tglobal, Tglobal
  | Th1, Th1
  | Th2, Th2
  | Tinstr, Tinstr
  | Tinit, Tinit
  | Tr1, Tr1
  | Tr2, Tr2
  | Tr3, Tr3
  | Tsp, Tsp => true
  | Tpc n1, Tpc n2
  | Tstack n1, Tstack n2 => Nat.eqb n1 n2
  | _, _ => false
  end.

Definition tag_neqb (t1 t2 :  Tag) : bool :=
  negb (tag_eqb t1 t2).

Definition calleeTag : Tag := Th1.

Definition TagSet : Type := list Tag.
Definition TagMap : Type := Zkeyed_map TagSet.

(* Map of memory tags *)
Record myPolicyState : Type :=
  {
  nextid: nat;
  pctags: TagSet;
  regtags: TagMap;
  memtags: TagMap;
  }.

Definition PolicyState := myPolicyState.

Instance etaPolicyState : Settable _ :=
  settable! Build_myPolicyState <nextid; pctags; regtags; memtags>.

(* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
Definition MPState : Type := MachineState * PolicyState.
Definition ms (mp : MPState) := fst mp.
Definition ps (mp : MPState) := snd mp.

(* TODO: Real policy. *)
(* ...
   TODO: Use [MonadNotations] *)

(* Definition callTags := [Tinstr; Tcall]. *)

(* TODO: Monadic syntax *)
Definition policyArith (p : PolicyState) (pc : word) (rd rs1 rs2 : Z) : option PolicyState :=
  tinstr <- map.get (memtags p) (word.unsigned pc);
  trs1 <- map.get (regtags p) rs1;
  trs2 <- map.get (regtags p) rs2;
  trd <- map.get (regtags p) rd;
  match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2, trd with
  | [Tinstr], false, false, [] => Some p
  | _, _, _, _ => None
  end.

Definition policyBranch (p : PolicyState) (pc : word) (rs1 rs2 : Z) : option PolicyState :=
  tinstr <- map.get (memtags p) (word.unsigned pc);
  trs1 <- map.get (regtags p) rs1;
  trs2 <- map.get (regtags p) rs2;
  match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2 with
  | [Tinstr], false, false => Some p
  | _, _, _ => None
  end.

Definition policyImmArith (p : PolicyState) (pc : word) (rd rs (*imm*) : Z) : option PolicyState :=
  tinstr <- map.get (memtags p) (word.unsigned pc);
  let tpc := pctags p in
  trs <- map.get (regtags p) rs;
  trd <- map.get (regtags p) rd;
  match tinstr with
  | [Tinstr] =>
    match forallb (tag_neqb Tsp) trs, forallb (tag_neqb Tsp) trd with
    | true, true => Some (p <| regtags := map.put (regtags p) rd [] |>)
    | _, _ => None
    end
  | [Tinstr; Th2] =>
    match existsb (tag_eqb Th2) tpc, trs with
    | true, [Tsp] => Some (p <| pctags := filter (tag_neqb Th2) tpc |>
                             <| regtags := map.put (regtags p) rd [Tsp] |>)
    | _, _ => None
    end
  | [Tinstr; Tr2] =>
    match existsb (tag_eqb Tr2) tpc, trs with
    | true, [Tsp] => Some (p <| pctags := filter (tag_neqb Tr2) tpc ++ [Tr3] |>
                             <| regtags := map.put (regtags p) rd [Tsp] |>)
    | _, _ => None
    end
  | _ => None
  end.

Definition policyJal (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
  match pctags p, map.get (memtags p) (word.unsigned pc) with
  | [Tpc old], Some [Tinstr; Tcall] =>
    let newid := S (nextid p) in (* TODO: This is not next but last! *)
    Some (p <| nextid := newid |>
            <| pctags := [Tpc newid; Th1] |>
            <| regtags := map.put (regtags p) rd [Tpc old] |>)
  | _, _ => None
  end.

Definition policyJalr (p : PolicyState) (pc : word) (rd rs : Z) : option PolicyState :=
  tinstr <- map.get (memtags p) (word.unsigned pc);
  let tpc := pctags p in
  ttarget <- map.get (regtags p) rs;
  treturn <- map.get (regtags p) rd;
  match tinstr with
  | [Tinstr] =>
    match tpc, ttarget, treturn with
    | [Tpc _], [], [] => Some p
    | _, _, _ => None
    end
  | [Tinstr; Tr3] =>
    match tpc, ttarget with
    | [Tpc _; Tr3], [Tpc old] => Some (p <| pctags := [Tpc old] |>
                                         <| regtags := map.put (regtags p) rd [] |>)
    | _, _ => None
    end
  | _ => None
  end.

Definition policyLoad (p : PolicyState) (pc rsdata : word) (rd rs imm : Z) : option PolicyState :=
  tinstr <- map.get (memtags p) (word.unsigned pc);
  let addr := word.unsigned rsdata + imm in
  taddr <- map.get (memtags p) addr;
  let tpc := pctags p in
  trs <- map.get (regtags p) rs;
  match tinstr with
  | [Tinstr] =>
    match tpc, taddr with
    | [Tpc pcdepth], [Tstack memdepth] =>
      if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
      else None
    | [Tpc _], [Tglobal] => Some p
    | _, _ => None
    end
  | [Tinstr; Tr1] =>
    match trs, taddr with
    | [Tsp], [Tpc _] => Some (p <| pctags := pctags p ++ [Tr2] |>
                                <| regtags := map.put (regtags p) rd taddr |>)
    | _, _ => None
    end
  | _ => None
  end.

Definition policyStore (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
  tinstr <- map.get (memtags p) (word.unsigned pc);
  let addr := word.unsigned rddata + imm in
  tmem <- map.get (memtags p) addr;
  let tpc := pctags p in
  trs <- map.get (regtags p) rs;
  taddr <- map.get (regtags p) rd;
  match tinstr with
  | [Tinstr] =>
    (* TODO: Relaxed in order for program to work: no stack-indexed writes? *)
    (* TODO: Restrictions on [trs] here? *)
    match tpc, existsb (tag_eqb Tsp) taddr, trs, tmem with
    | [Tpc pcdepth], (*false*)_, [(*_*)], [Tstack memdepth] =>
      if Nat.eqb pcdepth memdepth then Some p else None
    | [Tpc _], _, [], [Tglobal] => Some p
    | _, _, _, _ => None
    end
  | [Tinstr; Th1] =>
    match existsb (tag_eqb Th1) tpc, trs, taddr with
    | true, [Tpc depth], [Tsp] => Some (p <| pctags := filter (tag_neqb Th1) tpc ++ [Th2] |>
                                          <| memtags := map.put (memtags p) addr [Tpc depth] |>)
    | _, _, _ => None
    end
  | [Tinstr; Tinit] =>
    (* Special case for stack space initialization and clearing as
       part of the blessed sequences. At the moment, this relies on an
       external well-formedness criterion (i.e., these instructions
       are only used as part of the entry and return sequences to
       initialize or clear (and tag in both cases) stack space, but
       the micropolicy does not control whether this is the case, or
       whether the right slots are being written to. *)
    match tpc, taddr with
    | [Tpc depth], [Tsp] => Some (p <| memtags := map.put (memtags p) addr [Tstack depth] |>)
    | _, _ => None
    end
  | _ => None
  end.

Definition decodeI (w : w32) : option InstructionI :=
  match decode RV32IM (LittleEndian.combine 4 w) with
  | IInstruction i => Some i
  | _ => None
  end.

Definition pstep (mp : MPState) : option PolicyState :=
  let '(m, p) := mp in
  let pc := getPc m in
  w <- loadWord (getMem m) pc;
  i <- decodeI w;
  match i with
  | Add  rd rs1 rs2 | Sub rd rs1 rs2 | Sll rd rs1 rs2 | Slt rd rs1 rs2
  | Sltu rd rs1 rs2 | Xor rd rs1 rs2 | Or  rd rs1 rs2 | Srl rd rs1 rs2
  | Sra  rd rs1 rs2 | And rd rs1 rs2
    => policyArith p pc rd rs1 rs2
  | Beq  rs1 rs2 _ | Bne  rs1 rs2 _ | Blt rs1 rs2 _ | Bge rs1 rs2 _
  | Bltu rs1 rs2 _ | Bgeu rs1 rs2 _
    => policyBranch p pc rs1 rs2
  | Addi rd rs _ | Slti rd rs _ | Sltiu rd rs _ | Xori rd rs _ | Ori rd rs _
  | Andi rd rs _ | Slli rd rs _ | Srli  rd rs _ | Srai rd rs _
    => policyImmArith p pc rd rs
  | Jal rd _
    => policyJal p pc rd
  | Jalr rd rs _
    => policyJalr p pc rd rs
  | Lb rd rs imm | Lh rd rs imm | Lw rd rs imm | Lbu rd rs imm | Lhu rd rs imm
    => rsdata <- map.get (getRegs m) rs;
       policyLoad p pc rsdata rd rs imm
  | Sb rd rs imm | Sh rd rs imm | Sw rd rs imm
    => rddata <- map.get (getRegs m) rd;
       policyStore p pc rddata rd rs imm
  | _
    => None
  end.

Definition mpstep (mp : MPState) : option (MPState * Observation) :=
  p' <- pstep mp;
  match step (ms mp) with
  | (m', o) => Some (m', p', o)
  end
.

Axiom mpstepCompat :
  forall m p o m' p',
    mpstep (m,p) = Some (m',p',o) ->
    step m = (m',o).

(* TODO: More interesting well-formedness condition *)
Definition WFInitMPState (mp:MPState) := True.

End EagerInitGlobal.
