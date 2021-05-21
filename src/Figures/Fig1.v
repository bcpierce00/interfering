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

From StackSafety Require Import Trace MachineImpl EagerInit.
Import RISCV.
Import EagerInit.

Let stack_init : Z := 100.
Let data_words : nat := 8.

(* Writing programs more abstractly *)
Let RARG : Z := 19.
Let RRES : Z := 18.
Let RTMP : Z := 20.

Definition program : list Instruction := map IInstruction
  (* 00 *) [Jal RA 8; (* Call main *)
  (* 04 *) Beq 0 0 0; (* Finish execution (loop) *)
  (* main *)
  (* 08 *) Sw SP RA 0; (* H1 *)
  (* 12 *) Addi SP SP 12; (* H2 *)
  (* 16 *) Addi RTMP 0 42; (* For brevity, initial values in sequence *)
  (* 20 *) Sw SP RTMP (-8); (* Init x *)
  (* 24 *) Sw SP 0 (-4); (* Init y *)
  (* 28 *) Addi RARG 0 10;
  (* 32 *) Jal RA 36; (* Call f *)
  (* 36 *) Sw SP RRES (-4); (* y not really necessary *)
  (* 40 *) Lw RTMP SP (-8);
  (* 44 *) Add RRES RRES RTMP;
  (* 48 *) Sw SP 0 (-8); (* Clear x *)
  (* 52 *) Sw SP 0 (-4); (* Clear y *)
  (* 56 *) Lw RA SP (-12); (* R1 *)
  (* 60 *) Addi SP SP (-12); (* R2 *)
  (* 64 *) Jalr RA RA 0; (* R3 *)
  (* f *)
  (* 68 *) Sw SP RA 0; (* H1 *)
  (* 72 *) Addi SP SP 4; (* H2 *)
  (* 76 *) Sw SP 0 (-12); (* Addi RTMP 0 0; *)
  (* 80 *) Add RRES RARG RARG;
  (* 84 *) Lw RA SP (-4); (* R1 *)
  (* 88 *) Addi SP SP (-4); (* R2 *)
  (* 92 *) Jalr RA RA 0] (* R3 *)
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

Definition tags : list (list Tag) :=
  [callTags; instrTags]
    ++ [h1Tags; h2Tags; instrTags; initTags; initTags]
    ++ [instrTags; callTags]
    ++ repeat instrTags 3
    ++ [initTags; initTags; r1Tags; r2Tags; r3Tags]
    ++ [h1Tags; h2Tags; instrTags; instrTags; r1Tags; r2Tags; r3Tags]
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

(* Gets stuck at instruction 76 *)
Compute (run 30 (initialRiscvMachine program) (initialPumpPolicy tags) nil).
