Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.
Import List.ListNotations.
Require Import Bool.

From StackSafety Require Import MachineModule PolicyModule.

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

Module RISCV <: Machine.
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
  Definition Value := Word.

  Definition vtow (v:Value) : Word := v.
  Definition ztow (z:Z) : Word := z.
  Definition wtoz (w:Word) : Z := w.
  
  (* Parameter Word *)
  Definition Addr : Type := Word.

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
  Proof.
    apply Z.eqb_eq.
  Qed.

  (* Lemma not_weq_implies_neq : *)
  (*   forall w1 w2, *)
  (*     weq w1 w2 = false -> w1 <> w2. *)
  (* Proof.  *)
  (*   intros w1 w2 HEqb HEq. unfold weq in *. *)
  (*   apply Z.eqb_eq in HEq. *)
  (*   rewrite HEq in HEqb. *)
  (*   congruence. *)
  (* Qed. *)

  Definition wle (w1 w2: Word) : bool :=
    orb (wlt w1 w2) (weq w1 w2).

  (*
    Parameter wplus : Word -> nat -> Word.
    Parameter wminus : Word -> nat -> Word.
   *)
  Definition wplus (w : Word) (n : Z) : Word :=
    w + n.

  Definition wminus (w : Word) (n : Z) : Word :=
    w - n.

  Lemma wplus_neq : forall w (n : Z),
      (n > 0)%Z -> w <> wplus w n.
  Proof.
    intros w n H Contra.
    unfold wplus in *.
    lia.
  Qed.

  (* Definition wtoa (w:Word) : option Addr := Some w. *)

  (* Definition alt := wlt. *)
  (* Definition aeq := weq. *)
  (* Definition AddrEqDec := WordEqDec. *)
  (* Definition aeq_implies_eq := weq_implies_eq. *)
  (* Definition not_aeq_implies_neq := not_weq_implies_neq. *)
  (* Definition ale := wle. *)
  (* Definition aplus := wplus. *)
  (* Definition aplus_neq := wplus_neq. *)
  (* Definition aminus := wminus. *)
  
  Definition Register : Type := Word.

  Definition RA := 1.
  Definition SP := 2.
  Definition regEqb : Register -> Register -> bool := Z.eqb.

  (* TODO *)
  (* Parameter is_callee_save : Register -> bool. *)
  Definition is_callee_save (r : Register) : bool := false. (* FIXME *)

  Definition callee_save (r : Register) : bool :=
    match r with
    | 1 | 2 => true
    | _ => is_callee_save r
    end.

  Lemma RA_callee_save : callee_save RA = true.
  Proof.
    reflexivity.
  Qed.

  Lemma SP_callee_save : callee_save SP = true.
  Proof.
    reflexivity.
  Qed.

  Inductive Element :=
  | Mem (a:Addr)
  | Reg (r:Register)
  | PC.

  (* Derive Show for Element. *)

  Definition keqb (k1 k2 : Element) : bool :=
    match k1, k2 with
    | Mem a1, Mem a2 => Z.eqb a1 a2
    | Reg r1, Reg r2 => regEqb r1 r2
    | PC, PC => true
    | _, _ => false
    end.

  (* Axiom keqb_implies_eq : *)
  (*   forall k1 k2, *)
  (*     keqb k1 k2 = true -> k1 = k2. *)
  (* Axiom not_keqb_implies_neq : *)
  (*   forall k1 k2, *)
  (*     keqb k1 k2 = false -> k1 <> k2. *)

  (* A Value is a Word. *)
  (* Definition Value : Type := Word. *)
  (* Definition vtow (v : Value) : Word := v. *)

  (* We use a risc-v machine as our machine state *)
  Definition MachineState := RiscvMachine.


  (* Project what we care about from the RiscV state. *)
  Definition proj (m:  MachineState) (k: Element):  Word :=
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

  Definition projw (m:MachineState) (k:Element) := vtow (proj m k).

  Instance etaMachineState : Settable _ :=
    settable! mkRiscvMachine <getRegs; getPc; getNextPc; getMem; getXAddrs; getLog>.

  (* Maybe name this pullback instead *)
  Definition jorp (m : MachineState) (k : Element) (v : Value) : MachineState :=
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

  Definition jorpw (m : MachineState) (k : Element) (w : Word) : MachineState :=
    match k with
    | Mem a =>
      withMem
        (unchecked_store_byte_list (word.of_Z a)
                                   (Z32s_to_bytes [w]) (getMem m)) m
    | Reg r => 
      withRegs (map.put (getRegs m) r (word.of_Z w)) m
    | PC =>
      withPc (word.of_Z w) m
    end.
  
  Definition getElements (m : MachineState) : list Element :=
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

  Definition Event : Type := Register*Word.
  
  Definition event_eqb (e1 e2 : Event) : bool :=
    let '(a1, v1) := e1 in
    let '(a2, v2) := e1 in
    andb (weq a1 a2) (weq v1 v2).
  
  (* Observations are values, or silent (tau) *)
  Inductive Observation : Type := 
  | Out (w:Event)
  | Tau.

  Definition obs_eqb (o1 o2 : Observation) : bool :=
    match o1, o2 with
    | Out e1, Out e2 => event_eqb e1 e2
    | Tau, Tau => true
    | _, _ => false
    end.

  (* Definition w32_eqb (w1 w2 : w32) : bool := *)
  (*   let l1 := HList.tuple.to_list w1 in *)
  (*   let l2 := HList.tuple.to_list w2 in *)
  (*   let l12 := List.combine l1 l2 in *)
  (*   forallb (fun '(b1, b2) => Byte.eqb b1 b2) l12. *)

  (* Definition memAddr_eqb (mem mem' : DefaultMemImpl32.Mem) (addr : word32) : bool := *)
  (*   match loadWord mem addr, loadWord mem' addr with *)
  (*   | Some w, Some w' => w32_eqb w w' *)
  (*   | _, _ => false *)
  (*   end. *)

  Definition listify1 {A} (m : Zkeyed_map A)
    : list (Z * A) :=
    List.rev (map.fold (fun acc z v => (z,v) :: acc) nil m).
  
  (* For now we will only monitor registers for changes. We could monitor
     some memory, but we can't monitor the stack. *)
  Definition findDiff (mOld mNew : MachineState) : option (Register*Word) :=
    match find (fun '(reg,_) => negb (weq (proj mOld (Reg reg)) (proj mNew (Reg reg))))
               (listify1 (getRegs mNew)) with
    | Some (r, _) =>
      Some (r, proj mNew (Reg r))
    | None => None
    end.

  Definition FunID := nat.
  Definition StackID := nat.

  (* Definition EntryMap := Addr -> bool. *)

  Definition StackMap := Addr -> option StackID.

  (* Inductive CodeAnnotation := *)
  (* | call *)
  (* | retrn *)
  (* | yield *)
  (* | scall (f: MachineState -> Addr -> bool) *)
  (* | normal *)
  (* . *)
  
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

  (* Definition justRet (mc m: MachineState) : Prop := *)
  (*   proj m PC = wplus (proj mc PC) 4 /\ proj m (Reg SP) = proj mc (Reg SP). *)

  (* Definition justRet_dec mc m : {justRet mc m} + {~ justRet mc m}. *)
  (* Proof. *)
  (*   unfold justRet. *)
  (*   destruct (WordEqDec (proj m PC) (wplus (proj mc PC) 4)); *)
  (*     destruct (WordEqDec (proj m (Reg SP)) (proj mc (Reg SP))); *)
  (*     try solve [left; auto]; *)
  (*     right; intros [? ?]; auto. *)
  (* Qed. *)

  Inductive Operation : Type :=
  | Call (f:FunID) (reg_args:list Register) (stk_args:list (Register*Z*Z))
  | Tailcall (f:FunID) (reg_args:list Register) (stk_args:list (Register*Z*Z))
  | Return
  | Alloc (off:Z) (sz:Z)
  | Dealloc (off:Z) (sz:Z)
  .

  Derive Show for Operation.

  Definition Operations := list Operation.

  Definition CodeMap := Addr -> option Operations.
  
  (* TODO: operations *)
  (* A Machine State can step to a new Machine State plus an Observation. *)
  Definition step (m : MachineState) : MachineState * list Operation * Observation :=
    (* returns option unit * state *)
    let '(_, s') := Run.run1 RV32IM m in
    if Z.eqb (word.unsigned (getPc m))
         (word.unsigned (getPc s'))
    then
      (s', [], Tau)
    else
      match findDiff m s' with
      | Some v => (s', [], Out v)
      | None => (s', [], Tau)
      end.

End RISCV.

Module RISCVTagged (P : TagPolicy RISCV) <: Machine.
  Import P.
  Export RISCV.
  
  Definition Word := Word.
  Definition Value : Type := (Word * Tag).
  
  Definition vtow (v:Value) : Word := fst v.
  Definition ztow (z:Z) : Word := ztow z.
  Definition wtoz (w:Word) : Z := w.
  
  Definition Addr := Addr.
  
  Instance ShowWord : Show word :=
    {| show x := show (word.signed x) |}.

  Definition wlt := wlt.
  Definition weq := weq.
  Definition WordEqDec := WordEqDec.
  Definition weq_implies_eq := weq_implies_eq.
  Definition wle := wle.
  Definition wplus := wplus.
  Definition wminus := wminus.
  Definition wplus_neq := wplus_neq.  
  Definition Register := Register.
  Definition RA := RA.
  Definition SP := RA.
  Definition regEqb := regEqb.
  Definition callee_save := callee_save.
  Definition RA_callee_save := RA_callee_save.
  Definition SP_callee_save := SP_callee_save.

  Inductive Element :=
  | Mem (a:Addr)
  | Reg (r:Register)
  | PC.

  Definition coercion1 (k:Element) :=
    match k with
    | Mem a => RISCV.Mem a
    | Reg r => RISCV.Reg r
    | PC => RISCV.PC
    end.

  Definition coercion2 (k:RISCV.Element) :=
    match k with
    | RISCV.Mem a => Mem a
    | RISCV.Reg r => Reg r
    | RISCV.PC => PC
    end.
  
  Coercion coercion1 : Element >-> RISCV.Element.
  Coercion coercion2 : RISCV.Element >-> Element.
  
  Definition keqb : Element -> Element -> bool := keqb.

  Definition MachineState : Type := MPState.

  Definition proj (m : MachineState) (k: Element) : Value :=
    let '(m,p) := m in
    (projw m k, projt p k).

  Definition projw (m : MachineState) (k: Element): Word :=
    let '(m,p) := m in
    projw m k.
  
  Definition jorp (m : MachineState) (k : Element) (v : Value) : MachineState :=
    let '(m,p) := m in
    let '(w,t) := v in
    let m' :=
      match k with
      | Mem a =>
          withMem
            (unchecked_store_byte_list (word.of_Z a)
                                       (Z32s_to_bytes [w]) (getMem m)) m
      | Reg r => 
          withRegs (map.put (getRegs m) r (word.of_Z w)) m
      | PC =>
          withPc (word.of_Z w) m
      end in
    let p' := jorpt p k t in
    (m',p').

  Definition jorpw (m : MachineState) (k : Element) (w : Word) : MachineState :=
    let '(m,p) := m in
    let m' :=
      match k with
      | Mem a =>
          withMem
            (unchecked_store_byte_list (word.of_Z a)
                                       (Z32s_to_bytes [w]) (getMem m)) m
      | Reg r => 
          withRegs (map.put (getRegs m) r (word.of_Z w)) m
      | PC =>
          withPc (word.of_Z w) m
      end in
    (m',p).
  
  Definition getElements (m : MachineState) : list Element :=
    let '(m,p) := m in
    map coercion2 (getElements m).

  Definition Event := Event.
  Definition event_eqb := event_eqb.
    
  Inductive Observation : Type := 
  | Out (w:Event)
  | Tau.

  Definition coercion3 (obs:RISCV.Observation) :=
    match obs with
    | RISCV.Out w => Out w
    | RISCV.Tau => Tau
    end.
  
  Coercion coercion3 : RISCV.Observation >-> Observation.
  
  Definition obs_eqb (o1 o2 : Observation) : bool :=
    match o1, o2 with
    | Out e1, Out e2 => event_eqb e1 e2
    | Tau, Tau => true
    | _, _ => false
    end.

  (* Definition w32_eqb (w1 w2 : w32) : bool := *)
  (*   let l1 := HList.tuple.to_list w1 in *)
  (*   let l2 := HList.tuple.to_list w2 in *)
  (*   let l12 := List.combine l1 l2 in *)
  (*   forallb (fun '(b1, b2) => Byte.eqb b1 b2) l12. *)

  (* Definition memAddr_eqb (mem mem' : DefaultMemImpl32.Mem) (addr : word32) : bool := *)
  (*   match loadWord mem addr, loadWord mem' addr with *)
  (*   | Some w, Some w' => w32_eqb w w' *)
  (*   | _, _ => false *)
  (*   end. *)

  Definition listify1 {A} (m : Zkeyed_map A)
    : list (Z * A) :=
    List.rev (map.fold (fun acc z v => (z,v) :: acc) nil m).
  
  (* For now we will only monitor registers for changes. We could monitor
     some memory, but we can't monitor the stack. *)
  Definition findDiff (mOld mNew : MachineState) : option (Register*Word) :=
    let '(mOld,pOld) := mOld in
    let '(mNew,pNew) := mNew in
    findDiff mOld mNew.

  Definition FunID := nat.
  Definition StackID := nat.

  (* Definition EntryMap := Addr -> bool. *)

  Definition StackMap := Addr -> option StackID.

  (* Inductive CodeAnnotation := *)
  (* | call *)
  (* | retrn *)
  (* | yield *)
  (* | scall (f: MachineState -> Addr -> bool) *)
  (* | normal *)
  (* . *)
  
  (* Stack ID of stack pointer *)
  Definition activeStack (sm: StackMap) (m: MachineState) :
    option StackID :=
    sm (projw m (Reg SP)).

  Definition stack_eqb : StackID -> StackID -> bool :=
    Nat.eqb.

  Definition optstack_eqb (o1 o2 : option StackID) : bool :=
    match o1, o2 with
    | Some n1, Some n2 => stack_eqb n1 n2
    | None, None => true
    | _, _ => false
    end.

  (* Definition justRet (mc m: MachineState) : Prop := *)
  (*   proj m PC = wplus (proj mc PC) 4 /\ proj m (Reg SP) = proj mc (Reg SP). *)

  (* Definition justRet_dec mc m : {justRet mc m} + {~ justRet mc m}. *)
  (* Proof. *)
  (*   unfold justRet. *)
  (*   destruct (WordEqDec (proj m PC) (wplus (proj mc PC) 4)); *)
  (*     destruct (WordEqDec (proj m (Reg SP)) (proj mc (Reg SP))); *)
  (*     try solve [left; auto]; *)
  (*     right; intros [? ?]; auto. *)
  (* Qed. *)

  Inductive Operation : Type :=
  | Call (f:FunID) (reg_args:list Register) (stk_args:list (Register*Z*Z))
  | Tailcall (f:FunID) (reg_args:list Register) (stk_args:list (Register*Z*Z))
  | Return
  | Alloc (off:Z) (sz:Z)
  | Dealloc (off:Z) (sz:Z)
  .

  Derive Show for Operation.

  Definition coercion4 (op : RISCV.Operation) :=
    match op with
    | RISCV.Call f reg_args stk_args => Call f reg_args stk_args
    | RISCV.Tailcall f reg_args stk_args => Call f reg_args stk_args
    | RISCV.Return => Return
    | RISCV.Alloc off sz => Alloc off sz
    | RISCV.Dealloc off sz => Dealloc off sz
    end.

  Coercion coercion4 : RISCV.Operation >-> Operation.
  
  Definition Operations := list Operation.

  Definition CodeMap := Addr -> option Operations.
  
  (* TODO: operations *)
  (* A Machine State can step to a new Machine State plus an Observation. *)
  Definition step (m : MachineState) : MachineState * list Operation * Observation :=
    let '(m',ops,obs) := mpstep m in
    (m',map coercion4 ops, coercion3 obs).
    
End RISCVTagged.
