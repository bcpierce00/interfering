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

Let global_words : nat := 1.
Let data_words : nat := 8.
(* TODO: Compute addresses (also based on program) *)
Let stash_addr := 128.
Let stack_init : Z := 132.

(* Writing programs more abstractly *)
Let RARG  : Z := 19.
Let RRES  : Z := 18.
Let RTMP1 : Z := 20.
Let RTMP2 : Z := 21.

(* In this program, arguments are passed on the stack (though return
   values are still passed by register). By convention, the caller
   stores the arguments immediately after its own frame (that is, from
   SP upwards). Those store instructions need a special tag so that
   they are allowed and tagged with the upcoming activation id. The
   blessed entry sequence then stores the RA on top of the designated
   number of arguments (and initializes any local state it may
   need). This means the offsets used by the blessed sequences depend
   on the arity of the function as well as the amount of local data
   needed. The related well-formedness checks are assumed here.  No
   restrictions are currently put on the use of passed arguments,
   e.g., in the case of pointers. *)
Definition program : list Instruction :=
  (* 000 *) [IInstruction (Sw SP 0 (-4)); (* Hackily initialize stash *)
  (* 004 *) IInstruction (Jal RA 8); (* Call main *)
  (* 008 *) IInstruction (Beq 0 0 0); (* Finish execution (loop) *)
  (* main *)
  (* 012 *) IInstruction (Sw SP RA 0); (* H1 *)
  (* 016 *) IInstruction (Addi SP SP 12); (* H2 *)
  (* 020 *) IInstruction (Sw SP 0 (-8)); (* Init x *)
  (* 024 *) IInstruction (Sw SP 0 (-4)); (* Init y *)
  (* 028 *) IInstruction (Addi RARG SP (-8));
  (* 032 *) IInstruction (Sw SP RARG 0); (* Store argument to f *)
  (* 036 *) IInstruction (Jal RA 44); (* First call to f *)
  (* 040 *) IInstruction (Sw SP 0 (-8)); (* Reset x *)
  (* 044 *) IInstruction (Addi RARG SP (-4));
  (* 048 *) IInstruction (Sw SP RARG 0); (* Store argument to f *)
  (* 052 *) IInstruction (Jal RA 28); (* Second call to f *)
  (* 056 *) IInstruction (Lw RRES SP (-8));
  (* 060 *) IInstruction (Sw SP 0 (-8)); (* Clear x *)
  (* 064 *) IInstruction (Sw SP 0 (-4)); (* Clear y *)
  (* 068 *) IInstruction (Lw RA SP (-12)); (* R1 *)
  (* 072 *) IInstruction (Addi SP SP (-12)); (* R2 *)
  (* 076 *) IInstruction (Jalr RA RA 0); (* R3 *)
  (* f *)
  (* 080 *) IInstruction (Sw SP RA 4); (* H1 (stores RA after the arg in SP+0) *)
  (* 084 *) IInstruction (Addi SP SP 8); (* H2 (increments SP by two: arg and RA) *)
  (* 088 *) IInstruction (Addi RTMP1 0 stash_addr);
  (* 092 *) IInstruction (Lw RTMP2 RTMP1 0); (* Keep the updated contents of stash in RTMP2 *)
  (* 096 *) IInstruction (Bne RTMP2 0 12); (* Does stash hold a value? *)
  (* 100 *) IInstruction (Lw RTMP2 SP (-8));
  (* 104 *) IInstruction (Sw RTMP1 RTMP2 0); (* If it doesn't, store argument *)
  (* 108 *) IInstruction (Addi RTMP1 0 5); (* Either way, write 5 to that address *)
  (* 112 *) IInstruction (Sw RTMP2 RTMP1 0);
  (* 116 *) IInstruction (Lw RA SP (-4)); (* R1 *)
  (* 120 *) IInstruction (Addi SP SP (-8)); (* R2 *)
  (* 124 *) IInstruction (Jalr RA RA 0)] (* R3 *)
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
  [instrTags; callTags; instrTags]
    (* main *)
    ++ [h1Tags; h2Tags; initTags; initTags]
    ++ [instrTags; argTags; callTags]
    ++ [instrTags; instrTags; argTags; callTags; instrTags]
    ++ [initTags; initTags; r1Tags; r2Tags; r3Tags]
    (* f *)
    ++ [h1Tags; h2Tags]
    ++ [instrTags; globalTags; instrTags]
    ++ [instrTags; globalTags; instrTags; instrTags]
    ++ [r1Tags; r2Tags; r3Tags]
    (* Data segment *)
    ++ repeat globalTags global_words
    ++ repeat initDataTags data_words.
Compute ((List.length program) + global_words + data_words)%nat.
Compute List.length tags.

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

(* Without a policy, the program will run to completion and the result
   register will contain the value 5, surreptitiously reassigned to x
   after it was reset to 0. *)
Compute (run 45 (initialRiscvMachine program) (initialPumpPolicy tags) nil).
