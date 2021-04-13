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

(* From StackSafety Require Import Trace MachineEagerInit. *)
From StackSafety Require Import Trace MachineEagerInit.

Let stack_init : Z := 136.
Let data_words : nat := 8.

(* Writing programs more abstractly *)
Let RARG  : Z := 19.
Let RRES  : Z := 18.
Let RTMP1 : Z := 20.
Let RTMP2 : Z := 21.

Let Nop : InstructionI := Addi 0 0 0.

(* In this program, stack frame initialization suffices to prevents
   the violation, even without a micropolicy. To keep composition and
   offsets simple, as well as use with both kinds of micropolicies
   (requiring initialization or not), leave room for those
   instructions and fill out as needed. Here, we leave some
   initialization in so as order to initialize tags, and
   surreptitiously turn it off so that both the eager policies will
   run and the vulnerability will be exhibited when a policy is not
   running. However, we will not do clearing. *)
Definition program : list Instruction := map IInstruction
  (* 000 *) [Jal RA 8; (* Call main *)
  (* 004 *) Beq 0 0 0; (* Finish execution (loop) *)
  (* main *)
  (* 008 *) Sw SP RA 0; (* H1 *)
  (* 012 *) Addi SP SP 8; (* H2 *)
  (* 016 *) Sw SP 0 (-4); (* Init x *)
  (* 020 *) Jal RA 28; (* Call f *)
  (* 024 *) Sw SP RRES (-4);
  (* 028 *) Jal RA 56; (* Call g *)
  (* (* 032 *) Sw SP 0 (-4); (* Clear x *) *) Nop;
  (* 036 *) Lw RA SP (-8); (* R1 *)
  (* 040 *) Addi SP SP (-8); (* R2 *)
  (* 044 *) Jalr RA RA 0; (* R3 *)
  (* f *)
  (* 048 *) Sw SP RA 0; (* H1 *)
  (* 052 *) Addi SP SP 8; (* H2 *)
  (* 056 *) Sw SP 0 (-4); (* Init y *)
  (* 060 *) Addi RRES 0 5;
  (* 064 *) Sw SP RRES (-4);
  (* (* 068 *) Sw SP 0 (-4); (* Clear y *) *) Nop;
  (* 072 *) Lw RA SP (-8); (* R1 *)
  (* 076 *) Addi SP SP (-8); (* R2 *)
  (* 080 *) Jalr RA RA 0; (* R3 *)
  (* g *)
  (* 084 *) Sw SP RA 0; (* H1 *)
  (* 088 *) Addi SP SP 8; (* H2 *)
  (* (* 092 *) Sw SP 0 (-4); (* Init z *) *) Nop;
  (* 096 *) Lw RTMP1 SP (-4);
  (* 100 *) Addi RTMP2 0 5;
  (* 104 *) Bne RTMP1 RTMP2 12;
  (* 108 *) Addi RRES 0 100;
  (* 112 *) Beq 0 0 8; (* Jump to return *)
  (* 116 *) Addi RRES 0 10; (* Cascade down to return *)
  (* (* 120 *) Sw SP 0 (-4); (* Clear z *) *) Nop;
  (* 124 *) Lw RA SP (-8); (* R1 *)
  (* 128 *) Addi SP SP (-8); (* R2 *)
  (* 132 *) Jalr RA RA 0] (* R3 *)
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
    (* main *)
    ++ [h1Tags; h2Tags]
    ++ [initTags; callTags; instrTags; callTags; instrTags]
    ++ [r1Tags; r2Tags; r3Tags]
    (* f *)
    ++ [h1Tags; h2Tags; initTags] ++ repeat instrTags 3 ++ [r1Tags; r2Tags; r3Tags]
    (* g *)
    ++ [h1Tags; h2Tags] ++ repeat instrTags 8 ++ [r1Tags; r2Tags; r3Tags]
    (* Stack *)
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

(* Gets stuck at instruction 96 by eager policy
   (unless prevented by init/clearing),
   without policy it runs to completion and returns 100 *)
Compute (run 40 (initialRiscvMachine program) (initialPumpPolicy tags) nil).
