Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.
Import List.ListNotations.

From StackSafety Require Import MachineModule RISCVMachine PolicyModule.

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

Module RISCVObs <: RISCV.
  Export RiscvMachine.

Axiom exception : forall {A}, string -> A.
Extract Constant exception =>
  "(fun l ->
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> Bytes.set s i c; copy (i+1) l
   in failwith (""Exception: "" ^ Bytes.to_string (copy 0 l)))".

  Definition Word := MachineInt.
  (* Parameter Word *)

  Instance ShowWord : Show word :=
    {| show x := show (word.signed x) |}.

  Definition wlt : Word -> Word -> bool := Z.ltb.
  (*  Parameter wlt : Word -> Word -> bool. *)

  Definition weq : Word -> Word -> bool := Z.eqb.
  (* Parameter weq : Word -> Word -> bool. *)

  Definition WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2} := Z.eq_dec.

  Lemma weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.
    apply Z.eqb_eq.
  Qed.

  Lemma not_weq_implies_neq :
    forall w1 w2,
      weq w1 w2 = false -> w1 <> w2.
  Proof. 
    intros w1 w2 HEqb HEq. unfold weq in *.
    apply Z.eqb_eq in HEq.
    rewrite HEq in HEqb.
    congruence.
  Qed.

  Definition wle (w1 w2: Word) : bool :=
    orb (wlt w1 w2) (weq w1 w2).

  (*
    Parameter wplus : Word -> nat -> Word.
    Parameter wminus : Word -> nat -> Word.
   *)
  Definition wplus (w : Word) (n : nat) : Word :=
    w + Z.of_nat n.

  Lemma wplus_neq : forall w (n : nat),
      (n > O)%nat -> w <> wplus w n.
  Proof.
    intros w n H Contra.
    unfold wplus in *.
    lia.
  Qed.

  Definition wminus (w : Word) (n : nat) : Word :=
    w - Z.of_nat n.

  Definition Addr : Type := Word.
  
  Definition Register : Type := Word.

  Definition RA := 1.
  Definition SP := 2.
  Definition regEq : Register -> Register -> bool := Z.eqb.

  Inductive Component:=
  | Mem (a:Addr)
  | Reg (r:Register)
  | PC.

  Derive Show for Component.

  Definition keqb (k1 k2 : Component) : bool :=
    match k1, k2 with
    | Mem a1, Mem a2 => Z.eqb a1 a2
    | Reg r1, Reg r2 => regEq r1 r2
    | PC, PC => true
    | _, _ => false
    end.

  Axiom keqb_implies_eq :
    forall k1 k2,
      keqb k1 k2 = true -> k1 = k2.
  Axiom not_keqb_implies_neq :
    forall k1 k2,
      keqb k1 k2 = false -> k1 <> k2.

  (* A Value is a Word. *)
  Definition Value : Type := Word.
  Definition vtow (v : Value) : Word := v.

  (* We use a risc-v machine as our machine state and a view as a map from its
     components to their values. *)
  Definition MachineState := RiscvMachine.
  Definition View := Component -> Value.

  (* Project what we care about from the RiscV state. *)
  Definition proj (m:  MachineState) (k: Component):  Value :=
    match k with
    | Mem a =>
      match (Spec.Machine.loadWord Spec.Machine.Execute (word.of_Z a)) m with
      | (Some w, _) => regToZ_signed (int32ToReg w)
      | (_, _) => 0
      end
    | Reg r =>
      match (Spec.Machine.getRegister r) m with
      | (Some w, _) => word.signed w
      | (_, _) => 0
      end
    | PC =>
      match (Spec.Machine.getPC) m with
      | (Some w, _) => word.signed w
      | (_, _) => 0
      end
    end.

  Definition projw := fun m k => vtow (proj m k).

  Lemma proj_vtow : forall m k, vtow (proj m k) = vtow (projw m k). Proof. intros;auto. Qed.

  (* Maybe name this pullback instead *)
  Definition jorp (m : MachineState) (k : Component) (v : Value) : MachineState :=
    match k with
    | Mem a =>
      withMem
        (unchecked_store_byte_list (word.of_Z a)
                                   (Z32s_to_bytes [v]) (getMem m)) m
    | Reg r => 
      withRegs (map.put (getRegs m) r (word.of_Z v)) m
    | PC =>
      withPc (word.of_Z v) m
    end.
  
  Definition getComponents (m : MachineState) : list Component :=
    (* PC *)
    let pc := [PC] in
    (* Non-zero registers. *)
    let regs :=
        List.map (fun x => Reg x) 
                 (List.rev
                    (map.fold (fun acc z v => z :: acc) nil 
                              (RiscvMachine.getRegs m))) in
    (* Non-zero memory-locs. *)
    let mem :=
        List.rev
          (map.fold (fun acc w v =>
                       let z := word.unsigned w in
                       if Z.eqb (snd (Z.div_eucl z 4)) 0
                       then (Mem z) :: acc else acc) nil 
                    (RiscvMachine.getMem m)) in
    pc ++ regs ++ mem.

  Definition ObsType : Type := Register*Value.

  Inductive Observation : Type := 
  | Out (w:ObsType) 
  | Tau.

  Definition obs_eqb (o1 o2 : Observation) :=
    match o1, o2 with
    | Out (a1, v1), Out (a2, v2) => andb (weq a1 a2) (weq v1 v2)
    | Tau, Tau => true
    | _, _ => false
    end.

  Definition w32_eqb (w1 w2 : w32) : bool :=
    let l1 := HList.tuple.to_list w1 in
    let l2 := HList.tuple.to_list w2 in
    let l12 := List.combine l1 l2 in
    forallb (fun '(b1, b2) => Byte.eqb b1 b2) l12.

  Definition memAddr_eqb (mem mem' : DefaultMemImpl32.Mem) (addr : word32) : bool :=
    match loadWord mem addr, loadWord mem' addr with
    | Some w, Some w' => w32_eqb w w'
    | _, _ => false
    end.

  Definition listify1 {A} (m : Zkeyed_map A)
    : list (Z * A) :=
    List.rev (map.fold (fun acc z v => (z,v) :: acc) nil m).
  
  (* For now we will only monitor registers for changes. We could monitor
     some memory, but we can't monitor the stack. *)
  Definition findDiff (mOld mNew : MachineState) : option (Register*Value) :=
    match find (fun '(reg,_) => negb (weq (proj mOld (Reg reg)) (proj mNew (Reg reg))))
               (listify1 (getRegs mNew)) with
    | Some (r, _) =>
      Some (r, proj mNew (Reg r))
    | None => None
    end
    .

  (* A Machine State can step to a new Machine State plus an Observation. *)
  Definition step (m : RiscvMachine) : RiscvMachine * Observation :=
    (* returns option unit * state *)
    match Run.run1 RV32IM m with
    | (_, s') =>
      if Z.eqb (word.unsigned (getPc m))
               (word.unsigned (getPc s'))
      then
        (s', Tau)
      else          
        match findDiff m s' with
        | Some v => (s', Out v)
        | None => (s', Tau)
        end
    end
  .

  Definition FunID := nat.
  Definition StackID := nat.

  Definition EntryMap := Addr -> bool.

  Definition StackMap := Addr -> option StackID.

  Inductive CodeAnnotation :=
  | call
  | retrn
  | yield
  | scall (f: MachineState -> Addr -> bool)
  | normal
  .
  
  Definition CodeMap := Addr -> option CodeAnnotation.

  (* Stack ID of stack pointer *)
  Definition activeStack (sm: StackMap) (m: MachineState) :
    option StackID :=
    sm (proj m (Reg SP)).

  Definition stack_eqb : StackID -> StackID -> bool :=
    Nat.eqb.

  Definition optstack_eqb (o1 o2 : option StackID) : bool :=
    match o1, o2 with
    | Some n1, Some n2 => stack_eqb n1 n2
    | None, None => true
    | _, _ => false
    end.

  Definition justRet (mc m: MachineState) : Prop :=
    proj m PC = wplus (proj mc PC) 4 /\ proj m (Reg SP) = proj mc (Reg SP).

  Definition justRet_dec mc m : {justRet mc m} + {~ justRet mc m}.
  Proof.
    unfold justRet.
    destruct (WordEqDec (proj m PC) (wplus (proj mc PC) 4));
      destruct (WordEqDec (proj m (Reg SP)) (proj mc (Reg SP)));
      try solve [left; auto];
      right; intros [? ?]; auto.
  Qed.
End RISCVObs.

Module TPEagerObs := TagPolicyEager RISCVObs.
Module TPLazyFixedObs := TagPolicyLazyFixed RISCVObs.

(*Module TagPolicyObs <: Policy RISCVObs.
  Import RISCVObs.
  
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

  Open Scope list.
  
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
    | [Tinstr; Th1] =>
      match existsb (tag_eqb Th1) tpc, trs with
      | true, [Tsp] => Some (p <| pctags := filter (tag_neqb Th1) tpc ++ [Th2] |>
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
      (*    Some (p <| regtags := map.put (regtags p) rd [] |>) (* ERROR *) *)

      match tpc, taddr with
      | [Tpc pcdepth], [Tstack memdepth] =>
        if Nat.leb pcdepth memdepth then Some (p <| regtags := map.put (regtags p) rd [] |>)
        else None
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

  Definition getdef {T} m k (vdef : T) :=
    match map.get m k with
    | Some v => v
    | None => vdef
    end.

  Definition policyStore (p : PolicyState) (pc rddata : word) (rd rs imm : Z) : option PolicyState :=
    tinstr <- map.get (memtags p) (word.unsigned pc);
    let addr := word.unsigned rddata + imm in
    (* tmem <- map.get (memtags p) addr; *)
    let tmem := getdef (memtags p) addr [] in
    let tpc := pctags p in
    trs <- map.get (regtags p) rs;
    taddr <- map.get (regtags p) rd;
    match tinstr with
    | [Tinstr] =>
      (* TODO: Relaxed in order for program to work: no stack-indexed writes? *)
      match tpc, existsb (tag_eqb Tsp) taddr, trs, tmem with
      | [Tpc depth], (*false*)_, [], [] =>
        Some (p <| memtags := map.put (memtags p) addr [Tpc depth] |>)
      | [Tpc depth], (*false*)_, [], [Tpc memdepth] =>
        if Nat.eqb depth memdepth then  
          Some (p <| memtags := map.put (memtags p) addr [Tpc depth] |>)
        else None  
      | _, _, _, _ => None
      end
    | [Tinstr; Th2] =>
      (*    trace (show (tpc, existsb (tag_eqb Th1) tpc, trs, taddr) ++ nl)%string *)
      ( 
        match existsb (tag_eqb Th2) tpc, trs, taddr with
        | true, cons (Tpc depth) nil, cons Tsp nil =>
          Some (p <| pctags := filter (tag_neqb Th2) tpc ++ [Th3] |>
                  <| memtags := map.put (memtags p) addr [Tpc depth] |>)
        | _, _, _ =>
          None
        end)
    | [Tinstr; Th3] =>
      (* trace (show (tpc, existsb (tag_eqb Th3) tpc, trs, taddr) ++ nl)%string  *)
      ( 
        match tpc, taddr with
        | ([Tpc depth; Th3]), cons Tsp nil =>
          Some (p <| pctags := filter (tag_neqb Th3) tpc ++ [Th4] |>
                  <| memtags := map.put (memtags p) addr [Tpc depth] |>)
        | _, _ =>
          None
        end)
    | [Tinstr; Th4] =>
      (*    trace (show (tpc, existsb (tag_eqb Th1) tpc, trs, taddr) ++ nl)%string *)
      ( 
        match tpc, taddr with
        | ([Tpc depth; Th4]), cons Tsp nil =>
          Some (p <| pctags := filter (tag_neqb Th4) tpc |>
                  <| memtags := map.put (memtags p) addr [Tpc depth] |>)
        | _, _ =>
          None
        end      
      )
    | _ => None
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
End TagPolicyObs.*)
