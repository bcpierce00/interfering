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

From StackSafety Require Import Trace MachineEagerInitArgGlobalObs.

Let global_words : nat := 1.
Let data_words : nat := 8.
(* TODO: Compute addresses (also based on program) *)
Let out_addr := 152.
Let stack_init : Z := 156.

(* Writing programs more abstractly *)
Let RARG  : Z := 19.
Let RRES  : Z := 18.
Let RTMP1 : Z := 20.
Let RTMP2 : Z := 21.

(* Long running example with no stack clearing on exit and return
   values passed by register.
   TODO: Initialize OUT to non-zero value to catch first store. *)
Definition program : list Instruction :=
  (* 000 *) [IInstruction (Jal RA 8); (* Call main *)
  (* 004 *) IInstruction (Beq 0 0 0); (* Finish execution (loop) *)
  (* main *)
  (* 008 *) IInstruction (Sw SP RA 0); (* H1 *)
  (* 012 *) IInstruction (Addi SP SP 12); (* H2 *)
  (* 016 *) IInstruction (Addi RTMP1 0 42);
  (* 020 *) IInstruction (Sw SP RTMP1 (-8)); (* Init x *)
  (* 024 *) IInstruction (Sw SP 0 (-4)); (* Init y *)
  (* 028 *) IInstruction (Sw SP 0 0); (* Store argument z to f *)
  (* 032 *) IInstruction (Jal RA 36); (* Call f *)
  (* 036 *) IInstruction (Sw SP RRES (-4)); (* Store result in y *)
  (* 040 *) IInstruction (Lw RTMP1 SP (-8)); (* Load x *)
  (* 044 *) IInstruction (Add RRES RRES RTMP1);
  (* 048 *) IInstruction (Addi RTMP2 0 out_addr);
  (* 052 *) IInstruction (Sw RTMP2 RRES 0); (* Print x + y *)
  (* 056 *) IInstruction (Lw RA SP (-12)); (* R1 *)
  (* 060 *) IInstruction (Addi SP SP (-12)); (* R2 *)
  (* 064 *) IInstruction (Jalr RA RA 0); (* R3 *)
  (* f *)
  (* 068 *) IInstruction (Sw SP RA 4); (* H1 (stores RA after the arg in SP+0) *)
  (* 072 *) IInstruction (Addi SP SP 12); (* H2 (increments SP by three: arg, RA and local w) *)
  (* 076 *) IInstruction (Sw SP 0 (-4)); (* Init w *)
  (* 080 *) IInstruction (Addi RTMP1 0 17);
  (* 084 *) IInstruction (Sw SP RTMP1 0); (* Store argument v to g *)
  (* 088 *) IInstruction (Jal RA 36); (* Call g *)
  (* 092 *) IInstruction (Sw SP RRES (-4)); (* Set w to return value *)
  (* 096 *) IInstruction (Lw RTMP1 SP (-12)); (* Load argument z *)
  (* 100 *) IInstruction (Addi RTMP2 0 out_addr);
  (* 104 *) IInstruction (Sw RTMP2 RTMP1 0); (* Print z *)
  (* 108 *) IInstruction (Add RRES RRES RTMP1); (* Compute return value (g's return + z) *)
  (* 112 *) IInstruction (Lw RA SP (-8)); (* R1 *)
  (* 116 *) IInstruction (Addi SP SP (-12)); (* R2 *)
  (* 120 *) IInstruction (Jalr RA RA 0); (* R3 *)
  (* g *)
  (* 124 *) IInstruction (Sw SP RA 4); (* H1 (stores RA after the arg in SP+0) *)
  (* 128 *) IInstruction (Addi SP SP 8); (* H2 (increments SP by two: arg and RA) *)
  (* 132 *) IInstruction (Lw RRES SP (-8)); (* Load argument v *)
  (* 136 *) IInstruction (Addi RRES RRES 1); (* Increment and return *)
  (* 140 *) IInstruction (Lw RA SP (-4)); (* R1 *)
  (* 144 *) IInstruction (Addi SP SP (-8)); (* R2 *)
  (* 148 *) IInstruction (Jalr RA RA 0)] (* R3 *)
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
    ++ [h1Tags; h2Tags; instrTags; initTags; initTags]
    ++ [argTags; callTags]
    ++ repeat instrTags 5
    ++ [r1Tags; r2Tags; r3Tags]
    (* f *)
    ++ [h1Tags; h2Tags; initTags; instrTags]
    ++ [argTags; callTags]
    ++ repeat instrTags 5
    ++ [r1Tags; r2Tags; r3Tags]
    (* g *)
    ++ [h1Tags; h2Tags; instrTags; instrTags; r1Tags; r2Tags; r3Tags]
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

Compute (run 35 (initialRiscvMachine program) (initialPumpPolicy tags) nil).
