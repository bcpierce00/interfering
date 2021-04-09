Require Import Coq.Lists.List.
Require Import coqutil.Z.Lia.
Import ListNotations.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
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

From StackSafety Require Import Trace MachineEagerInit.

Definition fib6_riscv_concrete: list MachineInt := [ (* TODO should be "word32", not MachineInt *)
  Ox"00600993";         (* li s3,6 *)
  Ox"00000a13";         (* li s4,0 *)
  Ox"00100913";         (* li s2,1 *)
  Ox"00000493";         (* li s1,0 *)
  Ox"0140006f";         (* j 101e0 <main+0x44> *)
  Ox"012a0ab3";         (* add s5,s4,s2 *)
  Ox"00090a13";         (* mv s4,s2 *)
  Ox"000a8913";         (* mv s2,s5 *)
  Ox"00148493";         (* addi s1,s1,1 *)
  Ox"ff34c8e3"          (* blt s1,s3,101d0 <main+0x34> *)
].

(*
Notation x0 := (WO~0~0~0~0~0)%word.
Notation s1 := (WO~0~1~0~0~1)%word.
Notation s2 := (WO~1~0~0~1~0)%word.
Notation s3 := (WO~1~0~0~1~1)%word.
Notation s4 := (WO~1~0~1~0~0)%word.
Notation s5 := (WO~1~0~1~0~1)%word.
*)

Goal False.
  set (l := List.map (decode RV32IM) fib6_riscv_concrete).
  cbv in l.
  (* decoder seems to work :) *)
Abort.

Let stack_init : Z := 100.
Let data_words : nat := 32.

(* Writing programs more abstractly *)
Let RARG : Z := 19.
Let RRES : Z := 18.
Let RTMP : Z := 20.

Definition fib_riscv (n : Z) : list Instruction :=
  (* Main *)
  (* 00 *) [IInstruction (Addi RARG 0 n);
  (* 04 *) IInstruction (Jal RA 8);
  (* 08 *) IInstruction (Beq 0 0 0); (* Finish execution (loop) *)
  (* Fibonacci *)
  (* 12 *) IInstruction (Sw SP RA 0); (* H1 *)
  (* 16 *) IInstruction (Addi SP SP 8); (* H2 *)
  (* 20 *) IInstruction (Sw SP 0 (-4)); (* Init *)
  (* 24 *) IInstruction (Addi RTMP 0 2); (* Case selection *)
  (* 28 *) IInstruction (Blt RARG RTMP 44);
  (* - Recursive case *)
  (* 32 *) IInstruction (Addi RARG RARG (-1)); (* Decrement arg *)
  (* 36 *) IInstruction (Sw SP RARG (-4)); (* Save arg in stack *)
  (* 40 *) IInstruction (Jal RA (-28)); (* First call *)
  (* 44 *) IInstruction (Lw RARG SP (-4)); (* Restore arg from stack *)
  (* 48 *) IInstruction (Sw SP RRES (-4)); (* Save res in stack *)
  (* 52 *) IInstruction (Addi RARG RARG (-1)); (* Decrement arg *)
  (* 56 *) IInstruction (Jal RA (-44)); (* Second call *)
  (* 60 *) IInstruction (Lw RTMP SP (-4)); (* Restore res from stack *)
  (* 64 *) IInstruction (Add RRES RRES RTMP); (* Add res *)
  (* 68 *) IInstruction (Beq 0 0 8); (* Jump to return *)
  (* 72 *) IInstruction (Addi RRES 0 1); (* Base case, cascades down to return *)
  (* 76 *) IInstruction (Sw SP 0 (-4)); (* Init *)
  (* 80 *) IInstruction (Lw RA SP (-8)); (* R1 *)
  (* 88 *) IInstruction (Addi SP SP (-8)); (* R2 *)
  (* 92 *) IInstruction (Jalr RA RA 0)] (* R3 *)
.

Let instrTags := [Tinstr].
Let callTags  := [Tinstr; Tcall].
Let h1Tags    := [Tinstr; Th1].
Let h2Tags    := [Tinstr; Th2].
Let r1Tags    := [Tinstr; Tr1].
Let r2Tags    := [Tinstr; Tr2].
Let r3Tags    := [Tinstr; Tr3].
Let initTags  := [Tinstr; Tinit].

Let initDataTags := [Tstack 0].

(* TODO: Better done in terms of call maps, etc., jointly with program *)
Definition fib_pump_bad : list (list Tag) :=
  [instrTags; callTags; instrTags; h1Tags] ++ repeat instrTags 17.

Definition fib_pump : list (list Tag) :=
  [instrTags; callTags; instrTags; h1Tags; h2Tags; initTags]
    ++ repeat instrTags 4
    ++ [callTags]
    ++ repeat instrTags 3
    ++ [callTags]
    ++ repeat instrTags 4
    ++ [initTags; r1Tags; r2Tags; r3Tags]
    ++ repeat initDataTags 32.

Goal False.
  (* We can get the memory dump as before *)
  set (l := map ZToReg (map encode (fib_riscv 6))).
  cbv in l.
  (* And it still decodes nicely *)
  set (l' := map (decode RV32IM) (map unsigned l)).
  cbv in l'.
Abort.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
(* TODO: Initialize register values? *)
Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.of_list [(0, wrap 0); (SP, wrap stack_init)];
  getPc := ZToReg 0;
  getNextPc := ZToReg 4;
  getMem := map.empty;
  getXAddrs := nil;
  getLog := nil;
|}.

Definition initialRiscvMachine(insts: list Instruction): RiscvMachine :=
  let words := map (@wrap 32) (map encode insts) ++ repeat (wrap 0) data_words in
  let imem := map unsigned words in
  putProgram imem (ZToReg 0) zeroedRiscvMachine.

Definition initialMemTags(tags: list (list Tag)): TagMap :=
  let fix aux (tags: list (list Tag)) (acc: Z * TagMap) : TagMap :=
      let '(addr, tagmap) := acc in
      match tags with
      | [] => tagmap
      | tagset :: tags' => aux tags' (addr + 4, map.put tagmap addr tagset)
      end
  in
  aux tags (0, map.empty).

Definition initialPumpPolicy(tags: list (list Tag)): PolicyState :=
  {| nextid := 0;
     pctags := [Tpc 0];
     regtags := map.put
                  (map.of_list (combine (map Z.of_nat (seq 0 32)) (repeat [] 32)))
                  SP [Tsp];
     memtags := initialMemTags tags |}.

(* success flag * final state *)
Fixpoint run (fuel: nat) (s: RiscvMachine) (p : PolicyState) (os : list Observation) : (list Observation * RiscvMachine * PolicyState * bool) :=
  match fuel with
  | O => (List.rev os, s, p, true)
  | S fuel' => match mpstep (s,p) with
               | Some ((s', p'), o) =>
                 run fuel' s' p' (o::os)
               | None => (List.rev os, s, p, false)
               end
  end.

Compute (run 360 (initialRiscvMachine (fib_riscv 6)) (initialPumpPolicy fib_pump_bad) nil). (* can't jump *)
Compute (run 360 (initialRiscvMachine (fib_riscv 6)) (initialPumpPolicy fib_pump) nil).
(* reg 18 *)
