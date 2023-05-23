From StackSafety Require Import RISCVMachine PolicyModule.

Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.
Import List.ListNotations.
(* FIXME? BoolNotations only from Coq 8.12 on
   Could break direct compatibility with Cerise (8.11) *)
Require Import Bool. Import BoolNotations.

Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
(* Require Import riscv.Spec.PseudoInstructions. *)
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

Definition trace := false.
Notation " S '!' A " := (if trace then Show.trace (S)%string A else A)
                          (at level 60).

Inductive version :=
| PER_ACTIVATION_TAG
| PER_DEPTH_TAG
| LOAD_NO_CHECK
| STORE_NO_UPDATE
.

Module TagPolicyLazyOrig <: TagPolicy RISCV.
  Import RISCV.
  Module PM := MachineModule.Properties RISCV.
  Import PM.
  
  Inductive stackKind : Type :=
  | Knormal
  | Krelarg
  | Krefarg (id:nat)
  .

  Definition stackKind_eqb (t1 t2 : stackKind) :=
    match t1, t2 with
    | Knormal, Knormal
    | Krelarg, Krelarg => true
    | Krefarg id1, Krefarg id2 => Nat.eqb id1 id2
    | _, _ => false
    end.

  Inductive myTag : Type :=
  | Tcall
  | Ttailcall
  | Th1
  | Th2
  | Th3 (* noop/entry point for tail calls *)
  | Tinstr
  | Tpc (n : nat)
  | Trai (* initial tag for return address *)
  | Tr1
  | Tr2
  | Tr3
  | Tsp
  | Tvar (n : nat) (* instruction tag for associating variable id with memory *)
  | Tstack (n : nat) (k : stackKind)
  | Tsetarg
  | Tref (d id : nat)
  .

  Definition tag_eqb (t1 t2 : myTag) : bool :=
    match t1, t2 with
    | Tcall, Tcall
    | Ttailcall, Ttailcall
    | Th1, Th1
    | Th2, Th2
    | Th3, Th3
    | Tinstr, Tinstr
    | Tr1, Tr1
    | Tr2, Tr2
    | Tr3, Tr3
    | Tsp, Tsp
    | Trai, Trai
    | Tsetarg, Tsetarg => true
    | Tref d1 id1, Tref d2 id2 => Nat.eqb d1 d2 && Nat.eqb id1 id2
    | Tpc n1, Tpc n2 => Nat.eqb n1 n2
    | Tstack n1 k1, Tstack n2 k2 => Nat.eqb n1 n2 && stackKind_eqb k1 k2
    | _, _ => false
    end.

  Definition tag_neqb (t1 t2 : myTag) : bool :=
    negb (tag_eqb t1 t2).

  Definition TagSet : Type := list myTag.
  Definition TagMap : Type := Zkeyed_map TagSet.

  Fixpoint TagSet_eqb l1 l2 :=
    match l1, l2 with
    | nil,nil => true
    | cons t1 l1', cons t2 l2' =>
        andb (tag_eqb t1 t2) (TagSet_eqb l1' l2')
    | _, _ => false
    end.

  Derive Show for stackKind.
  Derive Show for myTag.
  Derive Show for InstructionI.

  Fixpoint printTagSet (ts : TagSet) :=
    match ts with
    | t :: ts => (show t ++ printTagSet ts)%string
    | [] => ""
    end.

  Instance ShowTagSet : Show TagSet :=
    {| show ts := printTagSet ts |}.

  Definition Tag := TagSet.
  
  (* Map of memory tags *)
  Record myPolicyState : Type :=
    {
    nextid: nat;
    pctags: TagSet;
    regtags: TagMap;
    memtags: TagMap;
    }.

  Definition PolicyState := myPolicyState.

  Definition projt (p : PolicyState) (k : Element) : Tag :=
    let ts :=
      match k with
      | Mem a => map.get p.(memtags) a
      | Reg r => map.get p.(regtags) r
      | PC => Some p.(pctags)
      end in
    match ts with
    | Some ts => ts
    | None => []
    end.
  
  Instance etaPolicyState : Settable _ :=
    settable! Build_myPolicyState <nextid; pctags; regtags; memtags>.

  Definition jorpt (p : PolicyState) (k : Element) (t : Tag) : PolicyState :=
    match k with
    | Mem a => p <| memtags := map.put p.(memtags) a t |>
    | Reg r => p <| regtags := map.put p.(regtags) r t |>
    | PC => p <| pctags := t |>
    end.
  
  (* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
  Definition MPState : Type := MachineState * PolicyState.

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
          else ("Failstop in Arith" ++ nl) ! None
    | _, _, _ => ("Failstop in Arith" ++ nl) ! None
    end.

  Definition policyBranch (p : PolicyState) (pc : word) (rs1 rs2 : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    trs1 <- map.get (regtags p) rs1;
    trs2 <- map.get (regtags p) rs2;
    match tinstr, existsb (tag_eqb Tsp) trs1, existsb (tag_eqb Tsp) trs2 with
    | [Tinstr], false, false => Some p
    | _, _, _ => ("Failstop in Branch" ++ nl) ! None
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
      | _, _ => ("Failstop in ImmArith: just instr" ++ nl) ! None
      end
    | [Tinstr; Tvar id] =>
      match existsb (tag_eqb Tsp) trs, existsb (tag_eqb Tsp) trd, tpc with
      | true, false, [Tpc d] => Some (p <| regtags := map.put (regtags p) rd [Tref d id] |>)
      | _, _, _ => ("Failstop in ImmArith: Tvar" ++ nl) ! None
      end
    | [Tinstr; Th2] =>
      match tpc, trs, trd with
      | [Tpc depth; Th2], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Th3] |>)
      | _, _, _ => ("Failstop in ImmArith: Th2" ++ nl) ! None
      end
    | [Tinstr; Th3] =>
      match tpc, trs, trd with
      | [Tpc depth; Th3], _, _ => Some (p <| pctags := [Tpc depth] |>)
      | _, _, _ => ("Failstop in ImmArith: I@" ++ show tinstr ++ " pc@" ++ show tpc ++ " rs@" ++ show trs ++ " rd@" ++ show trd ++ nl) ! None
      end
    | [Tinstr; Tr1] =>
      (*trace ("r1" ++ nl)*)
      match tpc, trs, trd with
      | [Tpc depth], [Tsp], [Tsp] => Some (p <| pctags := [Tpc depth; Tr2] |>)
      | _, _, _ => ("Failstop in ImmArith: Tr1" ++ nl) ! None
      end
    | _ => ("Failstop in ImmArith: no tag" ++ nl) ! None
    end.
  
  Definition policyJalOrig (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
    match pctags p, map.get (memtags p) (word.unsigned pc) with
    | [Tpc old], Some [Tinstr; Tcall] =>
      let newid := S old in
      Some (p <| pctags := [Tpc newid; Th1] |>
              <| regtags := map.put (regtags p) rd [Tpc old] |>)
    | [Tpc old], Some [Tinstr; Ttailcall] =>
      (* Original policy is based on depth, no change on tail calls *)
      Some (p <| pctags := [Tpc old; Th3] |>)
    | _, _ => ("Failstop on Jal" ++ nl) ! None
    end.

  Definition policyJalFixed (p : PolicyState) (pc : word) (rd : Z) : option PolicyState :=
    match pctags p, map.get (memtags p) (word.unsigned pc) with
    | [Tpc old], Some [Tinstr; Tcall] =>
      let newid := S (nextid p) in
      Some (p <| nextid := newid |>
              <| pctags := [Tpc newid; Th1] |>
              <| regtags := map.put (regtags p) rd [Tpc old] |>)
    | [Tpc old], Some [Tinstr; Ttailcall] =>
        let newid := S (nextid p) in
        Some (p <| pctags := [Tpc newid; Th3] |>)
    | _, _ => ("Failstop on Jal" ++ nl) ! None
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
      | _, _, _ => ("Failstop on Jalr" ++ nl) ! None
      end
    | [Tinstr; Tr3] =>
      (*trace ("r3" ++ nl)*)
      match tpc, ttarget with
      | [Tpc current; Tr3], [Tpc old] => Some (p <| pctags := [Tpc old] |>
                                                 <| regtags := map.put (regtags p) rd [] |>)
      | _, _ => ("Failstop on Jalr: pc@" ++ show tpc ++ " rs@" ++ show ttarget
                                         ++ " rd@" ++ show treturn ++ nl) ! None
      end
    | _ => ("Failstop on Jalr" ++ nl) ! None
    end.
                                               
  Definition policyLoadCorrect (p : PolicyState) (pc rsdata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rsdata + imm in
    taddr <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, taddr with
      | [Tpc pcdepth], _, [Tstack memdepth Knormal] =>
          if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
          else ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
      | [Tpc pcdepth], _, [Tstack memdepth Krelarg] =>
          if Nat.eqb pcdepth (S memdepth) || Nat.eqb pcdepth memdepth
          then Some (p <| regtags := map.put (regtags p) rd [] |>)
          else ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
      | [Tpc pcdepth], _, [Tstack memdepth (Krefarg memid)] =>
          if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
          else match trs with
               | [Tref refdepth refid] =>
                   if Nat.eqb refdepth memdepth && Nat.eqb refid memid
                   then Some (p <| regtags := map.put (regtags p) rd [] |>)
                   else ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
               | _ => ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
               end
      | _, _, _ =>
        ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
      end
    | [Tinstr; Tr2] =>
      (*trace ("r2" ++ nl)*)
      match tpc, trs, taddr with
      | [Tpc depth; Tr2], [Tsp], [Tpc _]
      | [Tpc depth; Tr2], [Tsp], [Trai] =>
          Some (p <| pctags := [Tpc depth; Tr3] |>
                   <| regtags := map.put (regtags p) rd taddr |>)
      | _, _, _ => ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
      end
    | _ => ("Failstop on Load: no tag!" ++ nl) ! None
    end.

  Definition policyLoadNoCheck (p : PolicyState) (pc rsdata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rsdata + imm in
    taddr <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, taddr with
      | [Tpc pcdepth], _, [Tstack memdepth Knormal] =>
          Some (p <| regtags := map.put (regtags p) rd [] |>)
      | [Tpc pcdepth], _, [Tstack memdepth Krelarg] =>
          Some (p <| regtags := map.put (regtags p) rd [] |>)
      | [Tpc pcdepth], _, [Tstack memdepth (Krefarg memid)] =>
          if Nat.eqb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
          else match trs with
               | [Tref refdepth refid] =>
                   if Nat.eqb refdepth memdepth && Nat.eqb refid memid
                   then Some (p <| regtags := map.put (regtags p) rd [] |>)
                   else ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
               | _ => ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
               end
      | _, _, _ =>
        ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
      end
    | [Tinstr; Tr2] =>
      (*trace ("r2" ++ nl)*)
      match tpc, trs, taddr with
      | [Tpc depth; Tr2], [Tsp], [Tpc _]
      | [Tpc depth; Tr2], [Tsp], [Trai] =>
          Some (p <| pctags := [Tpc depth; Tr3] |>
                   <| regtags := map.put (regtags p) rd taddr |>)
      | _, _, _ => ("Failstop on Load: PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show taddr ++ nl) ! None
      end
    | _ => ("Failstop on Load: no tag!" ++ nl) ! None
    end.
  
  Definition policyStoreCorrect (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    tmem <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, tmem with
      | [Tpc memdepth], [], []
      | [Tpc memdepth], [], [Tstack _ _] =>
          Some (p <| memtags := map.put (memtags p) addr [Tstack memdepth Knormal] |>)
      | _, [Tref refdepth refid], []
      | _, [Tref refdepth refid], [Tstack _ _] =>
          Some (p <| memtags := map.put (memtags p) addr [Tstack refdepth (Krefarg refid)] |>)         
      | _, _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl) ! None
      end
    | [Tinstr; Tvar id] =>
        match tpc, tmem with
        | [Tpc memdepth], []
        | [Tpc memdepth], [Tstack _ _] =>
            Some (p <| memtags := map.put (memtags p) addr [Tstack memdepth (Krefarg id)] |>)         
        |  _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl) ! None
      end
    | [Tinstr; Tsetarg] =>
        match tpc, trs, tmem with
        | [Tpc memdepth], [], []
        | [Tpc memdepth], [], [Tstack _ _]
          => Some (p <| memtags := map.put (memtags p) addr [Tstack memdepth Krelarg] |>)
        | _, _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl) ! None
        end
    | [Tinstr; Th1] =>
        match tpc, trs, trd with
        | [Tpc depth; Th1], [Tpc _], [Tsp]
        | [Tpc depth; Th1], [Trai], [Tsp]
          => Some (p <| pctags := [Tpc depth; Th2] |>
                     <| memtags := map.put (memtags p) addr trs |>)
        | _, _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " rd@" ++ show trd ++ nl) ! None
        end
    | _ => ("Failstop on Store" ++ nl) ! None
    end.

  Definition policyStoreNoUpdate (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    tmem <- map.get (memtags p) addr;
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    trd <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      match tpc, trs, tmem with
      | [Tpc memdepth], [], []
      | [Tpc memdepth], [], [Tstack _ _] =>
          Some (p <| memtags := map.put (memtags p) addr [Tstack memdepth Knormal] |>)
      | _, [Tref refdepth refid], []
      | _, [Tref refdepth refid], [Tstack _ _] =>
          Some (p <| memtags := map.put (memtags p) addr [Tstack refdepth (Krefarg refid)] |>)         
      | _, _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl) ! None
      end
    | [Tinstr; Tvar id] =>
        match tpc, tmem with
        | [Tpc memdepth], []
        | [Tpc memdepth], [Tstack _ _] =>
            Some (p <| memtags := map.put (memtags p) addr [Tstack memdepth (Krefarg id)] |>)         
        |  _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl) ! None
      end
    | [Tinstr; Tsetarg] =>
        match tpc, trs, tmem with
        | [Tpc memdepth], [], []
        | [Tpc memdepth], [], [Tstack _ _]
          => Some (p <| memtags := map.put (memtags p) addr [Tstack memdepth Krelarg] |>)
        | _, _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " addr@" ++ show tmem ++ nl) ! None
        end
    | [Tinstr; Th1] =>
        match tpc, trs, trd with
        | [Tpc depth; Th1], [Tpc _], [Tsp]
        | [Tpc depth; Th1], [Trai], [Tsp]
          => Some (p <| pctags := [Tpc depth; Th2] |>
                     <| memtags := map.put (memtags p) addr trs |>)
        | _, _, _ => ("Failstop on Store: I@" ++ show tinstr ++ " PC@" ++ show tpc ++ " rs@" ++ show trs ++ " rd@" ++ show trd ++ nl) ! None
        end
    | _ => ("Failstop on Store" ++ nl) ! None
    end.
  
  Definition decodeI (w : w32) : option InstructionI :=
    match decode RV32IM (LittleEndian.combine 4 w) with
    | IInstruction i => Some i
    | _ => None
    end.

  Definition v:version := LOAD_NO_CHECK.

  Definition pstep (m : MachineState) (p : PolicyState) : option PolicyState :=
    let pc := getPc m in
    w <- loadWord (getMem m) pc;
    i <- decodeI w;
    match i with
    | Add  rd rs1 rs2 | Sub rd rs1 rs2 | Sll rd rs1 rs2 | Slt rd rs1 rs2
    | Sltu rd rs1 rs2 | Xor rd rs1 rs2 | Or  rd rs1 rs2 | Srl rd rs1 rs2
    | Sra  rd rs1 rs2 | And rd rs1 rs2
      => policyArith p pc rd rs1 rs2
    | Beq  rs1 rs2 _ | Bne  rs1 rs2 _ | Blt rs1 rs2 _ | Bge rs1 rs2 _
    | Bltu rs1 rs2 _ | Bgeu rs1 rs2 _ => policyBranch p pc rs1 rs2
    | Addi rd rs _ | Slti rd rs _ | Sltiu rd rs _ | Xori rd rs _ | Ori rd rs _
    | Andi rd rs _ | Slli rd rs _ | Srli  rd rs _ | Srai rd rs _
      => policyImmArith p pc rd rs
    | Jal rd _ =>
        match v with
        | PER_DEPTH_TAG => policyJalOrig p pc rd
        | _ => policyJalFixed p pc rd
        end
    (*!! Original depth-based policy *)
    (*!       => policyJalOrig p pc rd*)
    | Jalr rd rs _
      => policyJalr p pc rd rs
    | Lb rd rs imm | Lh rd rs imm | Lw rd rs imm | Lbu rd rs imm | Lhu rd rs imm =>
        rsdata <- map.get (getRegs m) rs;
        match v with
        | LOAD_NO_CHECK => policyLoadNoCheck p pc rsdata rd rs imm
        | _ => policyLoadCorrect p pc rsdata rd rs imm
        end
    | Sb rd rs imm | Sh rd rs imm | Sw rd rs imm =>
        rddata <- map.get (getRegs m) rd;
        match v with
        | STORE_NO_UPDATE => policyStoreNoUpdate p pc rddata rd rs imm
        | _ => policyStoreCorrect p pc rddata rd rs imm
        end
    | _ => None
  end.
  
  Definition mpstep  (mp : MPState) : (MPState * list Operation * Observation) :=
    let '(m,p) := mp in
    match pstep m p with
    | Some p' =>
        let '(m',ops,o) := step m in
        (m',p',ops,o)
    | None => (m,p,nil,Tau)
    end.
  
  Definition WFInitMPState (mp:MPState) := True.

End TagPolicyLazyOrig.

Module RISCVLazyOrig := RISCVTagged TagPolicyLazyOrig.
