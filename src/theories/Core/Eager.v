From StackSafety Require Import RISCVMachine PolicyModule.

Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.
Import List.ListNotations.
Require Import Bool.

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

From QuickChick Require Import QuickChick.

Module TagPolicyEager (M: RISCV) <: Policy M.
  Import M.
  
  (* TODO: More interesting state/abstract *)
  Inductive Tag : Type :=
  | Tcall
  | Th1
  | Th2
  | Th3
  | Th4
  | Tinstr
  | Tpc (n : nat)
  | Tr1
  | Tr2
  | Tr3
  | Tr4
  | Tr5
  | Tsp
  | Tstack (n : nat)
  .

  Derive Show for Tag.
  Derive Show for InstructionI.

  Definition tag_eqb (t1 t2 :  Tag) : bool :=
    match t1, t2 with
    | Tcall, Tcall
    | Th1, Th1
    | Th2, Th2
    | Th3, Th3
    | Th4, Th4           
    | Tinstr, Tinstr
    | Tr1, Tr1
    | Tr2, Tr2
    | Tr3, Tr3
    | Tr4, Tr4
    | Tr5, Tr5
    | Tsp, Tsp => true
    | Tpc n1, Tpc n2
    | Tstack n1, Tstack n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Definition tag_neqb (t1 t2 :  Tag) : bool :=
    negb (tag_eqb t1 t2).

  Definition calleeTag : Tag := Th1.
  
  Definition TagSet : Type := list Tag.

  Fixpoint printTagSet (ts : TagSet) :=
    match ts with
    | t :: ts => (show t ++ printTagSet ts)%string
    | [] => ""
    end.

  Instance ShowTagSet : Show TagSet :=
    {| show ts := printTagSet ts |}.
  
  Definition TagMap : Type := Zkeyed_map TagSet.
  
  Fixpoint TagSet_eqb l1 l2 :=
    match l1, l2 with
    | nil,nil => true
    | cons t1 l1', cons t2 l2' =>
      andb (tag_eqb t1 t2) (TagSet_eqb l1' l2')
    | _, _ => false
    end.

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
  
  (* Project what we care about from the RiscV state. *)
  Definition pproj (p:  PolicyState) (k: Component):  TagSet :=
    match k with
    | Mem a =>
      match map.get (memtags p) a with
      | Some t => t
      | _ => nil
      end
    | Reg r =>
      match map.get (regtags p) r with
      | Some t => t
      | _ => nil
      end
    | PC => pctags p
    end.


  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.
  Definition ms (mp : MPState) := fst mp.
  Definition ps (mp : MPState) := snd mp.

  Definition policyArith (p : PolicyState) (pc : word) (rd rs1 rs2 : Z) : option PolicyState :=
    let tpc := pctags p in
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    trd <- map.get (regtags p) rd;
    match tinstr, tpc, trd with
    | [Tinstr], [Tpc _], [] =>
      if (negb (existsb (tag_eqb Tsp) trs1))
         && negb (existsb (tag_eqb Tsp) trs2)
          then Some p
          else (*trace ("Failstop in Arith" ++ nl)*) None
    | _, _, _ => (*trace ("Failstop in Arith" ++ nl)*) None
    end.

  Definition policyBranch (p : PolicyState) (pc : word) (rs1 rs2 : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2 with
    | [Tinstr], false, false => Some p
    | _, _, _ => (*trace ("Failstop in Branch" ++ nl)*) None
    end.

  Definition policyImmArith (p : PolicyState) (pc : word) (rd rs (*imm*) : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match existsb (tag_eqb Tsp) trs, existsb (tag_eqb Tsp) trd with
      | false, false => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | _, _ => (*trace ("Failstop in ImmArith: just instr" ++ nl)*) None
      end
    | [Tinstr; Th2] =>
      match tpc, trs, trd with
      | [Tpc depth; Th2], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Th3] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Th2" ++ nl)*) None
      end
    | [Tinstr; Tr3] =>
      (*trace ("r1" ++ nl)*)
      match tpc, trs, trd with
      | [Tpc depth], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Tr4] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Tr3" ++ nl)*) None
      end
    | _ => (*trace ("Failstop in ImmArith: no tag" ++ nl)*) None
    end.

  Definition policyJal (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
    match pctags p, map.get (memtags p) (word.unsigned pc) with
    | [Tpc old], Some [Tinstr; Tcall] =>
      let newid := S (nextid p) in (* TODO: This is not next but last! *)
      Some (p <| nextid := newid |>
              <| pctags := [Tpc newid; Th1] |>
              <| regtags := map.put (regtags p) rd [Tpc old] |>)
    | _, _ => (*trace ("Failstop on Jal" ++ nl)*) None
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
      | _, _, _ => trace ("Failstop on Jalr" ++ nl) None
      end
    | [Tinstr; Tr5] =>
      (*trace ("r3" ++ nl)*)
      match tpc, ttarget with
      | [Tpc _; Tr5], [Tpc old] => Some (p <| pctags := [Tpc old] |>
                                           <| regtags := map.put (regtags p) rd [] |>
                                           <| nextid := old |>)
      | _, _ => (*trace ("Failstop on Jalr: pc@" ++ show tpc ++ " rs@" ++ show ttarget
                                               ++ " rd@" ++ show treturn ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Jalr" ++ nl)*) None
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
      | _, [] => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | [Tpc pcdepth], [Tpc memdepth] => (* NOTE second tag is now Tpc, not Tstack *)
        if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
        else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      | _, _ =>
        (*trace ("Failstop on Load (other): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | [Tinstr; Tr4] =>
      (*trace ("r2" ++ nl)*)
      match tpc, trs, taddr with
      | [Tpc depth; Tr4], [Tsp], [Tpc _] => Some (p <| pctags := [Tpc depth; Tr5] |>
                                                    <| regtags := map.put (regtags p) rd taddr |>)
      | _, _, _ => (*trace ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Load: no tag!" ++ nl)*) None
    end.

  Definition policyStore (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    tmem <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, tmem with
      | _, [], [] => Some p (* No tagging or failstops outside the stack *)
      | [Tpc pcdepth], [], [Tpc memdepth] => (* Restore use of Tstack? *)
        if Nat.eqb pcdepth memdepth then Some p
        else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      | _, _, _ => (*trace ("Failstop on Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th1] =>
      match tpc, trs, trd with
      | [Tpc depth; Th1], [Tpc od], [Tsp] => Some (p <| pctags := [Tpc depth; Th2] |>
                                                     <| memtags := map.put (memtags p) addr [Tpc od] |>)
      | _, _, _ => (*trace ("Failstop on h1 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th3] =>
      match tpc, trs, trd with
      | [Tpc depth; Th3], _, [Tsp] => Some (p <| pctags := [Tpc depth; Th4] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h3 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th4] =>
      match tpc, trs, trd with
      | [Tpc depth; Th4], _, [Tsp] => Some (p <| pctags := [Tpc depth] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr1] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr1], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr2] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr2] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr2], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr3] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Store" ++ nl)*) None
  end.

  Definition decodeI (w : w32) : option InstructionI :=
    match decode RV32IM (LittleEndian.combine 4 w) with
    | IInstruction i => Some i
    | _ => None
    end.

  Definition pstep (mp : MPState) : option PolicyState :=
    (*  trace ("Entering pstep..." ++ nl)%string *)
    (
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
      end).

  Definition mpstep (mp : MPState) : option (MPState * Observation) :=
    let instr : string := 
        match loadWord (getMem (ms mp)) (getPc (ms mp)) with
        | Some w32 =>
          match decode RV32I (        LittleEndian.combine _ w32)  with
          | IInstruction inst =>
            show inst
          | _ => "<Not inst>"%string
          end
        | _ => "<Not inst2>"%string
        end in
      
    (*  trace ("Entering mpstep with" ++ show (word.unsigned (getPc (ms mp))) ++ " @ " ++ show (pctags (ps mp)) ++ " : " ++ instr ++ nl
        )%string*)
    (
      p' <- pstep mp; 
    match step (ms mp) with
    | (m', o) =>
      if Z.eqb (word.unsigned (getPc (ms mp)))
               (word.unsigned (getPc m'))
      then None (* error *)
      else Some (m', p', o)
    end
    )
  .

  Axiom mpstepCompat :
    forall m p o m' p',
      mpstep (m,p) = Some (m',p',o) ->
      step m = (m',o).


  (* TODO: More interesting well-formedness condition *)
  Definition WFInitMPState (mp:MPState) := True.
End TagPolicyEager.

Module TagPolicyEagerNoLoadCheck (M: RISCV) <: Policy M.
  Import M.

  (* TODO: More interesting state/abstract *)
  Inductive Tag : Type :=
  | Tcall
  | Th1
  | Th2
  | Th3
  | Th4
  | Tinstr
  | Tpc (n : nat)
  | Tr1
  | Tr2
  | Tr3
  | Tr4
  | Tr5
  | Tsp
  | Tstack (n : nat)
  .

  Derive Show for Tag.
  Derive Show for InstructionI.

  Definition tag_eqb (t1 t2 :  Tag) : bool :=
    match t1, t2 with
    | Tcall, Tcall
    | Th1, Th1
    | Th2, Th2
    | Th3, Th3
    | Th4, Th4           
    | Tinstr, Tinstr
    | Tr1, Tr1
    | Tr2, Tr2
    | Tr3, Tr3
    | Tr4, Tr4
    | Tr5, Tr5
    | Tsp, Tsp => true
    | Tpc n1, Tpc n2
    | Tstack n1, Tstack n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Definition tag_neqb (t1 t2 :  Tag) : bool :=
    negb (tag_eqb t1 t2).

  Definition calleeTag : Tag := Th1.
  
  Definition TagSet : Type := list Tag.

  Fixpoint printTagSet (ts : TagSet) :=
    match ts with
    | t :: ts => (show t ++ printTagSet ts)%string
    | [] => ""
    end.

  Instance ShowTagSet : Show TagSet :=
    {| show ts := printTagSet ts |}.
  
  Definition TagMap : Type := Zkeyed_map TagSet.
  
  Fixpoint TagSet_eqb l1 l2 :=
    match l1, l2 with
    | nil,nil => true
    | cons t1 l1', cons t2 l2' =>
      andb (tag_eqb t1 t2) (TagSet_eqb l1' l2')
    | _, _ => false
    end.

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
  
  (* Project what we care about from the RiscV state. *)
  Definition pproj (p:  PolicyState) (k: Component):  TagSet :=
    match k with
    | Mem a =>
      match map.get (memtags p) a with
      | Some t => t
      | _ => nil
      end
    | Reg r =>
      match map.get (regtags p) r with
      | Some t => t
      | _ => nil
      end
    | PC => pctags p
    end.


  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.
  Definition ms (mp : MPState) := fst mp.
  Definition ps (mp : MPState) := snd mp.

  Definition policyArith (p : PolicyState) (pc : word) (rd rs1 rs2 : Z) : option PolicyState :=
    let tpc := pctags p in
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    trd <- map.get (regtags p) rd;
    match tinstr, tpc, trd with
    | [Tinstr], [Tpc _], [] =>
      if (negb (existsb (tag_eqb Tsp) trs1))
         && negb (existsb (tag_eqb Tsp) trs2)
          then Some p
          else (*trace ("Failstop in Arith" ++ nl)*) None
    | _, _, _ => (*trace ("Failstop in Arith" ++ nl)*) None
    end.

  Definition policyBranch (p : PolicyState) (pc : word) (rs1 rs2 : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2 with
    | [Tinstr], false, false => Some p
    | _, _, _ => (*trace ("Failstop in Branch" ++ nl)*) None
    end.

  Definition policyImmArith (p : PolicyState) (pc : word) (rd rs (*imm*) : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match existsb (tag_eqb Tsp) trs, existsb (tag_eqb Tsp) trd with
      | false, false => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | _, _ => (*trace ("Failstop in ImmArith: just instr" ++ nl)*) None
      end
    | [Tinstr; Th2] =>
      match tpc, trs, trd with
      | [Tpc depth; Th2], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Th3] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Th2" ++ nl)*) None
      end
    | [Tinstr; Tr3] =>
      (*trace ("r1" ++ nl)*)
      match tpc, trs, trd with
      | [Tpc depth], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Tr4] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Tr3" ++ nl)*) None
      end
    | _ => (*trace ("Failstop in ImmArith: no tag" ++ nl)*) None
    end.

  Definition policyJal (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
    match pctags p, map.get (memtags p) (word.unsigned pc) with
    | [Tpc old], Some [Tinstr; Tcall] =>
      let newid := S (nextid p) in (* TODO: This is not next but last! *)
      Some (p <| nextid := newid |>
              <| pctags := [Tpc newid; Th1] |>
              <| regtags := map.put (regtags p) rd [Tpc old] |>)
    | _, _ => (*trace ("Failstop on Jal" ++ nl)*) None
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
      | _, _, _ => trace ("Failstop on Jalr" ++ nl) None
      end
    | [Tinstr; Tr5] =>
      (*trace ("r3" ++ nl)*)
      match tpc, ttarget with
      | [Tpc _; Tr5], [Tpc old] => Some (p <| pctags := [Tpc old] |>
                                           <| regtags := map.put (regtags p) rd [] |>
                                           <| nextid := old |> )
      | _, _ => (*trace ("Failstop on Jalr: pc@" ++ show tpc ++ " rs@" ++ show ttarget
                                               ++ " rd@" ++ show treturn ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Jalr" ++ nl)*) None
    end.

  Definition policyLoad (p : PolicyState) (pc rsdata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rsdata + imm in
    taddr <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    match tinstr with
    | [Tinstr] =>
      Some (p <| regtags := map.put (regtags p) rd [] |>) (* ERROR (LOAD_NO_CHECK, confidentiality) *)
    | [Tinstr; Tr4] =>
      (*trace ("r2" ++ nl)*)
      match tpc, trs, taddr with
      | [Tpc depth; Tr4], [Tsp], [Tpc _] => Some (p <| pctags := [Tpc depth; Tr5] |>
                                                    <| regtags := map.put (regtags p) rd taddr |>)
      | _, _, _ => (*trace ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Load: no tag!" ++ nl)*) None
    end.

  Definition policyStore (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    tmem <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, tmem with
      | _, [], [] => Some p
      | [Tpc pcdepth], [], [Tpc memdepth] =>
        if Nat.eqb pcdepth memdepth then Some p
        else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      | _, _, _ => (*trace ("Failstop on Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th1] =>
      match tpc, trs, trd with
      | [Tpc depth; Th1], [Tpc od], [Tsp] => Some (p <| pctags := [Tpc depth; Th2] |>
                                                     <| memtags := map.put (memtags p) addr [Tpc od] |>)
      | _, _, _ => (*trace ("Failstop on h1 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th3] =>
      match tpc, trs, trd with
      | [Tpc depth; Th3], _, [Tsp] => Some (p <| pctags := [Tpc depth; Th4] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h3 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th4] =>
      match tpc, trs, trd with
      | [Tpc depth; Th4], _, [Tsp] => Some (p <| pctags := [Tpc depth] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr1] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr1], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr2] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr2] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr2], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr3] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Store" ++ nl)*) None
  end.

  Definition decodeI (w : w32) : option InstructionI :=
    match decode RV32IM (LittleEndian.combine 4 w) with
    | IInstruction i => Some i
    | _ => None
    end.

  Definition pstep (mp : MPState) : option PolicyState :=
    (*  trace ("Entering pstep..." ++ nl)%string *)
    (
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
      end).

  Definition mpstep (mp : MPState) : option (MPState * Observation) :=
    let instr : string := 
        match loadWord (getMem (ms mp)) (getPc (ms mp)) with
        | Some w32 =>
          match decode RV32I (        LittleEndian.combine _ w32)  with
          | IInstruction inst =>
            show inst
          | _ => "<Not inst>"%string
          end
        | _ => "<Not inst2>"%string
        end in
      
    (*  trace ("Entering mpstep with" ++ show (word.unsigned (getPc (ms mp))) ++ " @ " ++ show (pctags (ps mp)) ++ " : " ++ instr ++ nl
        )%string*)
    (
      p' <- pstep mp; 
    match step (ms mp) with
    | (m', o) =>
      if Z.eqb (word.unsigned (getPc (ms mp)))
               (word.unsigned (getPc m'))
      then None (* error *)
      else Some (m', p', o)
    end
    )
  .

  Axiom mpstepCompat :
    forall m p o m' p',
      mpstep (m,p) = Some (m',p',o) ->
      step m = (m',o).

  (* TODO: More interesting well-formedness condition *)
  Definition WFInitMPState (mp:MPState) := True.
End TagPolicyEagerNoLoadCheck.

Module TagPolicyEagerNoStoreCheck (M: RISCV) <: Policy M.
  Import M.

    (* TODO: More interesting state/abstract *)
  Inductive Tag : Type :=
  | Tcall
  | Th1
  | Th2
  | Th3
  | Th4
  | Tinstr
  | Tpc (n : nat)
  | Tr1
  | Tr2
  | Tr3
  | Tr4
  | Tr5
  | Tsp
  | Tstack (n : nat)
  .

  Derive Show for Tag.
  Derive Show for InstructionI.

  Definition tag_eqb (t1 t2 :  Tag) : bool :=
    match t1, t2 with
    | Tcall, Tcall
    | Th1, Th1
    | Th2, Th2
    | Th3, Th3
    | Th4, Th4           
    | Tinstr, Tinstr
    | Tr1, Tr1
    | Tr2, Tr2
    | Tr3, Tr3
    | Tr4, Tr4
    | Tr5, Tr5
    | Tsp, Tsp => true
    | Tpc n1, Tpc n2
    | Tstack n1, Tstack n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Definition tag_neqb (t1 t2 :  Tag) : bool :=
    negb (tag_eqb t1 t2).

  Definition calleeTag : Tag := Th1.
  
  Definition TagSet : Type := list Tag.

  Fixpoint printTagSet (ts : TagSet) :=
    match ts with
    | t :: ts => (show t ++ printTagSet ts)%string
    | [] => ""
    end.

  Instance ShowTagSet : Show TagSet :=
    {| show ts := printTagSet ts |}.
  
  Definition TagMap : Type := Zkeyed_map TagSet.
  
  Fixpoint TagSet_eqb l1 l2 :=
    match l1, l2 with
    | nil,nil => true
    | cons t1 l1', cons t2 l2' =>
      andb (tag_eqb t1 t2) (TagSet_eqb l1' l2')
    | _, _ => false
    end.

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
  
  (* Project what we care about from the RiscV state. *)
  Definition pproj (p:  PolicyState) (k: Component):  TagSet :=
    match k with
    | Mem a =>
      match map.get (memtags p) a with
      | Some t => t
      | _ => nil
      end
    | Reg r =>
      match map.get (regtags p) r with
      | Some t => t
      | _ => nil
      end
    | PC => pctags p
    end.


  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.
  Definition ms (mp : MPState) := fst mp.
  Definition ps (mp : MPState) := snd mp.

  Definition policyArith (p : PolicyState) (pc : word) (rd rs1 rs2 : Z) : option PolicyState :=
    let tpc := pctags p in
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    trd <- map.get (regtags p) rd;
    match tinstr, tpc, trd with
    | [Tinstr], [Tpc _], [] =>
      if (negb (existsb (tag_eqb Tsp) trs1))
         && negb (existsb (tag_eqb Tsp) trs2)
          then Some p
          else (*trace ("Failstop in Arith" ++ nl)*) None
    | _, _, _ => (*trace ("Failstop in Arith" ++ nl)*) None
    end.

  Definition policyBranch (p : PolicyState) (pc : word) (rs1 rs2 : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2 with
    | [Tinstr], false, false => Some p
    | _, _, _ => (*trace ("Failstop in Branch" ++ nl)*) None
    end.

  Definition policyImmArith (p : PolicyState) (pc : word) (rd rs (*imm*) : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match existsb (tag_eqb Tsp) trs, existsb (tag_eqb Tsp) trd with
      | false, false => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | _, _ => (*trace ("Failstop in ImmArith: just instr" ++ nl)*) None
      end
    | [Tinstr; Th2] =>
      match tpc, trs, trd with
      | [Tpc depth; Th2], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Th3] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Th2" ++ nl)*) None
      end
    | [Tinstr; Tr3] =>
      (*trace ("r1" ++ nl)*)
      match tpc, trs, trd with
      | [Tpc depth], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Tr4] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Tr3" ++ nl)*) None
      end
    | _ => (*trace ("Failstop in ImmArith: no tag" ++ nl)*) None
    end.

  Definition policyJal (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
    match pctags p, map.get (memtags p) (word.unsigned pc) with
    | [Tpc old], Some [Tinstr; Tcall] =>
      let newid := S (nextid p) in (* TODO: This is not next but last! *)
      Some (p <| nextid := newid |>
              <| pctags := [Tpc newid; Th1] |>
              <| regtags := map.put (regtags p) rd [Tpc old] |>)
    | _, _ => (*trace ("Failstop on Jal" ++ nl)*) None
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
      | _, _, _ => trace ("Failstop on Jalr" ++ nl) None
      end
    | [Tinstr; Tr5] =>
      (*trace ("r3" ++ nl)*)
      match tpc, ttarget with
      | [Tpc _; Tr5], [Tpc old] => Some (p <| pctags := [Tpc old] |>
                                           <| regtags := map.put (regtags p) rd [] |>
                                           <| nextid := old |> )
      | _, _ => (*trace ("Failstop on Jalr: pc@" ++ show tpc ++ " rs@" ++ show ttarget
                                               ++ " rd@" ++ show treturn ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Jalr" ++ nl)*) None
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
      | _, [] => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | [Tpc pcdepth], [Tpc memdepth] => (* NOTE second tag is now Tpc, not Tstack *)
        if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
        else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      | _, _ =>
        (*trace ("Failstop on Load (other): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | [Tinstr; Tr4] =>
      (*trace ("r2" ++ nl)*)
      match tpc, trs, taddr with
      | [Tpc depth; Tr4], [Tsp], [Tpc _] => Some (p <| pctags := [Tpc depth; Tr5] |>
                                                    <| regtags := map.put (regtags p) rd taddr |>)
      | _, _, _ => (*trace ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Load: no tag!" ++ nl)*) None
    end.

  Definition policyStore (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    tmem <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      Some p
      (* ERROR (STORE_NO_CHECK, integrity)
         Alternative: Keep distinction between untagged memory (outside of
         stack, always allowed) and writes to stack memory (TPc on both tpc
         and tmem), and UPDATE the memory tags in the latter. *)
      (* match tpc, trs, tmem with *)
      (* | _, [], [] => Some p (* No tagging or failstops outside the stack *) *)
      (* | [Tpc pcdepth], [], [Tpc memdepth] => (* Restore use of Tstack? *) *)
      (*   (* if Nat.eqb pcdepth memdepth then *) *)
      (*     Some (p <| memtags := map.put (memtags p) addr [Tpc pcdepth] |>) *)
      (*   (* else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None *) *)
      (* end *)
    | [Tinstr; Th1] =>
      match tpc, trs, trd with
      | [Tpc depth; Th1], [Tpc od], [Tsp] => Some (p <| pctags := [Tpc depth; Th2] |>
                                                     <| memtags := map.put (memtags p) addr [Tpc od] |>)
      | _, _, _ => (*trace ("Failstop on h1 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th3] =>
      match tpc, trs, trd with
      | [Tpc depth; Th3], _, [Tsp] => Some (p <| pctags := [Tpc depth; Th4] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h3 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th4] =>
      match tpc, trs, trd with
      | [Tpc depth; Th4], _, [Tsp] => Some (p <| pctags := [Tpc depth] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr1] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr1], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr2] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr2] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr2], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr3] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Store" ++ nl)*) None    
  end.

  Definition decodeI (w : w32) : option InstructionI :=
    match decode RV32IM (LittleEndian.combine 4 w) with
    | IInstruction i => Some i
    | _ => None
    end.

  Definition pstep (mp : MPState) : option PolicyState :=
    (*  trace ("Entering pstep..." ++ nl)%string *)
    (
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
      end).

  Definition mpstep (mp : MPState) : option (MPState * Observation) :=
    let instr : string := 
        match loadWord (getMem (ms mp)) (getPc (ms mp)) with
        | Some w32 =>
          match decode RV32I (        LittleEndian.combine _ w32)  with
          | IInstruction inst =>
            show inst
          | _ => "<Not inst>"%string
          end
        | _ => "<Not inst2>"%string
        end in
      
    (*  trace ("Entering mpstep with" ++ show (word.unsigned (getPc (ms mp))) ++ " @ " ++ show (pctags (ps mp)) ++ " : " ++ instr ++ nl
        )%string*)
    (
      p' <- pstep mp; 
    match step (ms mp) with
    | (m', o) =>
      if Z.eqb (word.unsigned (getPc (ms mp)))
               (word.unsigned (getPc m'))
      then None (* error *)
      else Some (m', p', o)
    end
    )
  .

  Axiom mpstepCompat :
    forall m p o m' p',
      mpstep (m,p) = Some (m',p',o) ->
      step m = (m',o).


  (* TODO: More interesting well-formedness condition *)
  Definition WFInitMPState (mp:MPState) := True.
End TagPolicyEagerNoStoreCheck.

Module TagPolicyEagerNoInit (M: RISCV) <: Policy M.
  Import M.

    (* TODO: More interesting state/abstract *)
  Inductive Tag : Type :=
  | Tcall
  | Th1
  | Th2
  | Th3
  | Th4
  | Tinstr
  | Tpc (n : nat)
  | Tr1
  | Tr2
  | Tr3
  | Tr4
  | Tr5
  | Tsp
  | Tstack (n : nat)
  .

  Derive Show for Tag.
  Derive Show for InstructionI.

  Definition tag_eqb (t1 t2 :  Tag) : bool :=
    match t1, t2 with
    | Tcall, Tcall
    | Th1, Th1
    | Th2, Th2
    | Th3, Th3
    | Th4, Th4           
    | Tinstr, Tinstr
    | Tr1, Tr1
    | Tr2, Tr2
    | Tr3, Tr3
    | Tr4, Tr4
    | Tr5, Tr5
    | Tsp, Tsp => true
    | Tpc n1, Tpc n2
    | Tstack n1, Tstack n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Definition tag_neqb (t1 t2 :  Tag) : bool :=
    negb (tag_eqb t1 t2).

  Definition calleeTag : Tag := Th1.
  
  Definition TagSet : Type := list Tag.

  Fixpoint printTagSet (ts : TagSet) :=
    match ts with
    | t :: ts => (show t ++ printTagSet ts)%string
    | [] => ""
    end.

  Instance ShowTagSet : Show TagSet :=
    {| show ts := printTagSet ts |}.
  
  Definition TagMap : Type := Zkeyed_map TagSet.
  
  Fixpoint TagSet_eqb l1 l2 :=
    match l1, l2 with
    | nil,nil => true
    | cons t1 l1', cons t2 l2' =>
      andb (tag_eqb t1 t2) (TagSet_eqb l1' l2')
    | _, _ => false
    end.

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
  
  (* Project what we care about from the RiscV state. *)
  Definition pproj (p:  PolicyState) (k: Component):  TagSet :=
    match k with
    | Mem a =>
      match map.get (memtags p) a with
      | Some t => t
      | _ => nil
      end
    | Reg r =>
      match map.get (regtags p) r with
      | Some t => t
      | _ => nil
      end
    | PC => pctags p
    end.


  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.
  Definition ms (mp : MPState) := fst mp.
  Definition ps (mp : MPState) := snd mp.

  Definition policyArith (p : PolicyState) (pc : word) (rd rs1 rs2 : Z) : option PolicyState :=
    let tpc := pctags p in
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    trd <- map.get (regtags p) rd;
    match tinstr, tpc, trd with
    | [Tinstr], [Tpc _], [] =>
      if (negb (existsb (tag_eqb Tsp) trs1))
         && negb (existsb (tag_eqb Tsp) trs2)
          then Some p
          else (*trace ("Failstop in Arith" ++ nl)*) None
    | _, _, _ => (*trace ("Failstop in Arith" ++ nl)*) None
    end.

  Definition policyBranch (p : PolicyState) (pc : word) (rs1 rs2 : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2 with
    | [Tinstr], false, false => Some p
    | _, _, _ => (*trace ("Failstop in Branch" ++ nl)*) None
    end.

  Definition policyImmArith (p : PolicyState) (pc : word) (rd rs (*imm*) : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match existsb (tag_eqb Tsp) trs, existsb (tag_eqb Tsp) trd with
      | false, false => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | _, _ => (*trace ("Failstop in ImmArith: just instr" ++ nl)*) None
      end
    | [Tinstr; Th2] =>
      match tpc, trs, trd with
      | [Tpc depth; Th2], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Th3] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Th2" ++ nl)*) None
      end
    | [Tinstr; Tr3] =>
      (*trace ("r1" ++ nl)*)
      match tpc, trs, trd with
      | [Tpc depth], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Tr4] |>)
      | _, _, _ => (*trace ("Failstop in ImmArith: Tr3" ++ nl)*) None
      end
    | _ => (*trace ("Failstop in ImmArith: no tag" ++ nl)*) None
    end.

  Definition policyJal (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
    match pctags p, map.get (memtags p) (word.unsigned pc) with
    | [Tpc old], Some [Tinstr; Tcall] =>
      let newid := S (nextid p) in (* TODO: This is not next but last! *)
      Some (p <| nextid := newid |>
              <| pctags := [Tpc newid; Th1] |>
              <| regtags := map.put (regtags p) rd [Tpc old] |>)
    | _, _ => (*trace ("Failstop on Jal" ++ nl)*) None
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
      | _, _, _ => trace ("Failstop on Jalr" ++ nl) None
      end
    | [Tinstr; Tr5] =>
      (*trace ("r3" ++ nl)*)
      match tpc, ttarget with
      | [Tpc _; Tr5], [Tpc old] => Some (p <| pctags := [Tpc old] |>
                                           <| regtags := map.put (regtags p) rd [] |>)
      | _, _ => (*trace ("Failstop on Jalr: pc@" ++ show tpc ++ " rs@" ++ show ttarget
                                               ++ " rd@" ++ show treturn ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Jalr" ++ nl)*) None
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
      | _, [] => Some (p <| regtags := map.put (regtags p) rd [] |>)
      | [Tpc pcdepth], [Tpc memdepth] => (* NOTE second tag is now Tpc, not Tstack *)
        if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
        else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      | _, _ =>
        (*trace ("Failstop on Load (other): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | [Tinstr; Tr4] =>
      (*trace ("r2" ++ nl)*)
      match tpc, trs, taddr with
      | [Tpc depth; Tr4], [Tsp], [Tpc _] => Some (p <| pctags := [Tpc depth; Tr5] |>
                                                    <| regtags := map.put (regtags p) rd taddr |>)
      | _, _, _ => (*trace ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Load: no tag!" ++ nl)*) None
    end.

  Definition policyStore (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    tmem <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, tmem with
      | _, [], [] => Some p
      | [Tpc pcdepth], [], [Tpc memdepth] =>
        if Nat.eqb pcdepth memdepth then Some p
        else (*trace ("Failstop on Load (level): PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl)*) None
      | _, _, _ => (*trace ("Failstop on Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th1] =>
      match tpc, trs, trd with
      | [Tpc depth; Th1], [Tpc od], [Tsp] => Some (p <| pctags := [Tpc depth; Th2] |>
                                                     <| memtags := map.put (memtags p) addr [Tpc od] |>)
      | _, _, _ => (*trace ("Failstop on h1 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th3] =>
      match tpc, trs, trd with
      | [Tpc depth; Th3], _, [Tsp] => Some (p <| pctags := [Tpc depth; Th4] |>) (* ERROR (HEADER_NO_INIT, integrity) *)
      | _, _, _ => (*trace ("Failstop on h3 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Th4] =>
      match tpc, trs, trd with
      | [Tpc depth; Th4], _, [Tsp] => Some (p <| pctags := [Tpc depth] |>
                                              <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr1] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr1], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr2] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | [Tinstr; Tr2] =>
      match tpc, trs, trd with
      | [Tpc depth; Tr2], _, [Tsp] => Some (p <| pctags := [Tpc depth; Tr3] |>
                                              <| memtags := map.put (memtags p) addr [] |>)
      | _, _, _ => (*trace ("Failstop on h4 Store: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl)*) None
      end
    | _ => (*trace ("Failstop on Store" ++ nl)*) None
  end.

  Definition decodeI (w : w32) : option InstructionI :=
    match decode RV32IM (LittleEndian.combine 4 w) with
    | IInstruction i => Some i
    | _ => None
    end.

  Definition pstep (mp : MPState) : option PolicyState :=
    (*  trace ("Entering pstep..." ++ nl)%string *)
    (
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
      end).

  Definition mpstep (mp : MPState) : option (MPState * Observation) :=
    let instr : string := 
        match loadWord (getMem (ms mp)) (getPc (ms mp)) with
        | Some w32 =>
          match decode RV32I (        LittleEndian.combine _ w32)  with
          | IInstruction inst =>
            show inst
          | _ => "<Not inst>"%string
          end
        | _ => "<Not inst2>"%string
        end in
      
    (*  trace ("Entering mpstep with" ++ show (word.unsigned (getPc (ms mp))) ++ " @ " ++ show (pctags (ps mp)) ++ " : " ++ instr ++ nl
        )%string*)
    (
      p' <- pstep mp; 
    match step (ms mp) with
    | (m', o) =>
      if Z.eqb (word.unsigned (getPc (ms mp)))
               (word.unsigned (getPc m'))
      then None (* error *)
      else Some (m', p', o)
    end
    )
  .

  Axiom mpstepCompat :
    forall m p o m' p',
      mpstep (m,p) = Some (m',p',o) ->
      step m = (m',o).


  (* TODO: More interesting well-formedness condition *)
  Definition WFInitMPState (mp:MPState) := True.
End TagPolicyEagerNoInit.
