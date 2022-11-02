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

From StackSafety Require Import Trace RISCVMachine EagerInitGlobal.
Import RISCV.
Import EagerInitGlobal.

Let global_words : nat := 1.
Let data_words : nat := 8.
(* TODO: Compute addresses (also based on program) *)
Let stash_addr := 120.
Let stack_init : Z := 124.

(* Writing programs more abstractly *)
Let RARG  : Z := 19.
Let RRES  : Z := 18.
Let RTMP1 : Z := 20.
Let RTMP2 : Z := 21.

Definition program : list Instruction := map IInstruction
  (* 000 *) [Sw SP 0 (-4); (* Hackily initialize stash *)
  (* 004 *) Jal RA 8; (* Call main *)
  (* 008 *) Beq 0 0 0; (* Finish execution (loop) *)
  (* main *)
  (* 012 *) Sw SP RA 0; (* H1 *)
  (* 016 *) Addi SP SP 8; (* H2 *)
  (* 020 *) Addi RTMP1 0 1; (* For brevity, initial values in sequence *)
  (* 024 *) Sw SP RTMP1 (-4); (* Init x *)
  (* 028 *) Jal RA 40; (* First call to f *)
  (* 032 *) Lw RTMP1 SP (-4);
  (* 036 *) Sub RTMP1 0 RTMP1;
  (* 040 *) Sw SP RTMP1 (-4);
  (* 044 *) Jal RA 24; (* Second call to f *)
  (* 048 *) Lw RRES SP (-4);
  (* 052 *) Sw SP 0 (-4); (* Clear x *)
  (* 056 *) Lw RA SP (-8); (* R1 *)
  (* 060 *) Addi SP SP (-8); (* R2 *)
  (* 064 *) Jalr RA RA 0; (* R3 *)
  (* f *)
  (* 068 *) Sw SP RA 0; (* H1 *)
  (* 072 *) Addi SP SP 4; (* H2 *)
  (* 076 *) Addi RTMP1 0 stash_addr;
  (* 080 *) Lw RTMP2 RTMP1 0;
  (* 084 *) Bne RTMP2 0 16; (* Does stash hold a value? *)
  (* 088 *) Lw RTMP2 SP (-4);
  (* 092 *) Sw RTMP1 RTMP2 0; (* If it doesn't, store RA *)
  (* 096 *) Beq 0 0 12; (* Jump to return *)
  (* 100 *) Sw SP RTMP2 (-4); (* If it does, overwrite RA *)
  (* 104 *) Sw RTMP1 0 0; (* Cascade down to return *)
  (* 108 *) Lw RA SP (-4); (* R1 *)
  (* 112 *) Addi SP SP (-4); (* R2 *)
  (* 116 *) Jalr RA RA 0] (* R3 *)
.

Let instrTags  := [Tinstr].
Let callTags   := [Tinstr; Tcall].
Let h1Tags     := [Tinstr; Th1].
Let h2Tags     := [Tinstr; Th2].
Let r1Tags     := [Tinstr; Tr1].
Let r2Tags     := [Tinstr; Tr2].
Let r3Tags     := [Tinstr; Tr3].
Let initTags   := [Tinstr; Tinit].
Let globalTags := [Tglobal].

Let initDataTags := [Tstack 0].

Definition tags : list (list Tag) :=
  [instrTags; callTags; instrTags]
    ++ [h1Tags; h2Tags; instrTags; initTags]
    ++ [callTags; instrTags; instrTags; instrTags]
    ++ [callTags; instrTags]
    ++ [initTags; r1Tags; r2Tags; r3Tags]
    ++ [h1Tags; h2Tags]
    ++ repeat instrTags 8
    ++ [r1Tags; r2Tags; r3Tags]
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

(* Gets stuck at instruction 88 (operation on SP, before further misbehavior)
   With no policy, it would terminate and RRES would wrongly contain 1  *)
Compute (run 60 (initialRiscvMachine program) (initialPumpPolicy tags) nil).
