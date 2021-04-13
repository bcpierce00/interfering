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

From StackSafety Require Import Trace MachineEagerInitArgGlobal.

Let global_words : nat := 0.
Let data_words : nat := 8.
(* TODO: Compute addresses (also based on program) *)
(* Let stash_addr := 128. *)
Let stack_init : Z := 88.

(* Writing programs more abstractly *)
Let RARG : Z := 19.
Let RRES : Z := 18.
Let RTMP : Z := 20.

Definition program : list Instruction :=
  (* 000 *) [IInstruction (Jal RA 8); (* Call main *)
  (* 004 *) IInstruction (Beq 0 0 0); (* Finish execution (loop) *)
  (* main *)
  (* 008 *) IInstruction (Sw SP RA 0); (* H1 *)
  (* 012 *) IInstruction (Addi SP SP 8); (* H2 *)
  (* 016 *) IInstruction (Addi RTMP 0 5); (* For brevity, initial values in sequence *)
  (* 020 *) IInstruction (Sw SP RTMP (-4)); (* Init x *)
  (* 024 *) IInstruction (Sw SP RTMP 0); (* Store argument to f *)
  (* 028 *) IInstruction (Jal RA 20); (* Call f *)
  (* 032 *) IInstruction (Sw SP RRES (-4)); (* Assign result to x and return *)
  (* IInstruction (Sw SP 0 (-4)); (* Clear x *) *) (* No stack clearing *)
  (* 036 *) IInstruction (Lw RA SP (-8)); (* R1 *)
  (* 040 *) IInstruction (Addi SP SP (-8)); (* R2 *)
  (* 044 *) IInstruction (Jalr RA RA 0); (* R3 *)
  (* f *)
  (* 048 *) IInstruction (Sw SP RA 4); (* H1 (stores RA after the arg in SP+0) *)
  (* 052 *) IInstruction (Addi SP SP 8); (* H2 (increments SP by two: arg and RA) *)
  (* 056 *) IInstruction (Sw SP 0 0); (* Init y (could actually live in a register) *)
  (* 060 *) IInstruction (Lw RARG SP (-8)); (* Load a and operate *)
  (* 064 *) IInstruction (Add RRES RARG RARG);
  (* 068 *) IInstruction (Sw SP RRES 0); (* Store result in y (again, superfluous) *)
  (* 072 *) IInstruction (Sw SP 0 (-8)); (* Clear a *)
  (* 076 *) IInstruction (Lw RA SP (-4)); (* R1 *)
  (* 080 *) IInstruction (Addi SP SP (-8)); (* R2 *)
  (* 084 *) IInstruction (Jalr RA RA 0)] (* R3 *)
.

Let instrTags  := [Tinstr].
Let callTags   := [Tinstr; Tcall].
Let h1Tags     := [Tinstr; Th1].
Let h2Tags     := [Tinstr; Th2].
Let r1Tags     := [Tinstr; Tr1].
Let r2Tags     := [Tinstr; Tr2].
Let r3Tags     := [Tinstr; Tr3].
Let initTags   := [Tinstr; Tinit].
Let argTags    := [Tinstr; Targ].
Let globalTags := [Tglobal].

Let initDataTags := [Tstack 0].

Definition tags : list (list Tag) :=
  [callTags; instrTags]
    (* main *)
    ++ [h1Tags; h2Tags; instrTags; initTags]
    ++ [argTags; callTags; instrTags]
    ++ [r1Tags; r2Tags; r3Tags]
    (* f *)
    ++ [h1Tags; h2Tags; initTags]
    ++ repeat instrTags 4
    ++ [r1Tags; r2Tags; r3Tags]
    (* Data segment *)
    ++ repeat globalTags global_words
    ++ repeat initDataTags data_words.

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
  let words := map (@wrap 32) (map encode insts)
               ++ repeat (wrap 0) (global_words + data_words) in
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

Compute (run 25 (initialRiscvMachine program) (initialPumpPolicy tags) nil).
