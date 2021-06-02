From StackSafety Require Import MachineModule.

Require Import cap_machine.machine_parameters.
Require Import cap_machine.machine_run.
Require Import cap_machine.machine_base.
Require Import cap_machine.cap_lang.

From stdpp Require Import gmap fin_maps list countable.
Require Import ZArith. Open Scope Z.

Module Type Params.
(*  Parameter decodeInstr' : Z → instr.
  Parameter encodeInstr' : instr → Z.

  Parameter decode_encode_instr_inv :
    forall (i: instr), decodeInstr' (encodeInstr' i) = i.

  Parameter encodePerm : Perm → Z.
  Parameter encodePerm_inj : Inj eq eq encodePerm.

  Parameter encodeLoc : Locality → Z.
  Parameter encodeLoc_inj : Inj eq eq encodeLoc.

  Parameter decodePermPair : Z → Perm * Locality.
  Parameter encodePermPair : Perm * Locality → Z.

  Parameter decode_encode_permPair_inv :
    forall pl, decodePermPair (encodePermPair pl) = pl.*)

  Parameter params : MachineParameters.
  Instance paramsIs : MachineParameters := params.
End Params.

Module Cerise (P:Params) : Machine.
  Import P.

  (*  Axiom exception : forall {A}, string -> A.
      Extract Constant exception =>
      "(fun l ->
          let s = Bytes.create (List.length l) in
          let rec copy i = function
          | [] -> s
          | c :: l -> Bytes.set s i c; copy (i+1) l
          in failwith (""Exception: "" ^ Bytes.to_string (copy 0 l)))". *)


  Definition Word : Type := machine_base.Word.
  Definition Addr : Type := Addr.
  Definition Value : Type := Word.

  Definition wtoa (w:Word) :=
    match w with
    | inl z => z_to_addr z
    | inr (_,_,_,a) => Some a
    end.
      
  Definition vtow (v:Value) := v.
  
  Definition wlt (w1 w2:Word) : bool :=
    match w1,w2 with
    | inl z1, inl z2 => z1 <? z2
    | inr ((_),_,_,a1), inr ((_),_,_,a2) =>
      a1 <? a2
    | _,_ => false
    end.

  Definition alt a1 a2 := (a1 <? a2)%a.

  Definition weq (w1 w2:Word) : bool :=
    match w1,w2 with
    | inl z1, inl z2 => z1 =? z2
    | inr ((_),_,a1,_), inr ((_),_,a2,_) =>
      a1 =? a2
    | _,_ => false
    end.

  Definition aeq a1 a2 := (a1 =? a2)%a.
  
  Lemma WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.
  Proof. solve_decision. Qed.

  Definition AddrEqDec := addr_eq_dec.

  Axiom weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.

  Axiom not_weq_implies_neq :
    forall w1 w2,
      weq w1 w2 = false -> w1 <> w2.

  Axiom aeq_implies_eq :
    forall a1 a2,
      aeq a1 a2 = true -> a1 = a2.

  Axiom not_aeq_implies_neq :
    forall a1 a2,
      aeq a1 a2 = false -> a1 <> a2.
  
  Definition wle (w1 w2:Word) : bool := wlt w1 w2 || weq w1 w2.

  Definition ale a1 a2 := (a1 <=? a2)%a.
  
  Definition wplus (w:Word) (n:nat) : Word :=
    match w with
    | inl z => inl (z + (Z.of_nat n))
    | inr (p,base,ptr,bnd) =>
      let ptr' := (ptr + (Z.of_nat n))%a in
      inr (p,base,get_addr_from_option_addr None,bnd)
    end.

  Definition aplus a n :=
    get_addr_from_option_addr (a + (Z.of_nat n))%a.

  Definition wminus (w:Word) (n:nat) : Word :=
    match w with
    | inl z => inl (z - (Z.of_nat n))
    | inr (p,base,ptr,bnd) =>
      let ptr' := (ptr - (Z.of_nat n))%a in
      inr (p,base,get_addr_from_option_addr None,bnd)
    end.

  Definition aminus a n :=
    get_addr_from_option_addr (a + (Z.of_nat n))%a.
  
  Axiom wplus_neq : forall w (n : nat),
      (n > 0)%nat -> w <> wplus w n.

  Definition Register : Type := RegName.

  Lemma one_less : 1%nat <=? RegNum = true. Proof. auto. Qed.
  Lemma two_less : 1%nat <=? RegNum = true. Proof. auto. Qed.

  Definition RA : Register := R 1%nat one_less.
  Definition SP : Register := R 2%nat two_less.

  Definition regEq (r1 r2 : Register) : bool :=
    match r1,r2 with
    | R n1 _, R n2 _ => n1 =? n2
    | PC, PC => true
    | _, _ => false
    end.
  
  Inductive Component:=
  | Mem (a:Addr)
  | Reg (r:Register)
  | PC.

  Definition keqb (k1 k2:Component) : bool :=
    match k1, k2 with
    | Mem a1, Mem a2 => a1 =? a2
    | Reg r1, Reg r2 => regEq r1 r2
    | PC, Reg addr_reg.PC => true
    | Reg addr_reg.PC, PC => true
    | PC, PC => true
    | _, _ => false
    end.

  Definition MachineState : Type := (machine_base.Reg * machine_base.Mem).

  Definition View := Component -> Value.

  Definition proj : MachineState -> Component -> Value :=
    fun '(rs,mem) k =>
      match k with
      | Reg r => rs !r! r
      | Mem m => mem !m! m
      | PC => rs !r! addr_reg.PC
      end.
  
  Definition projw : MachineState -> Component -> Word := proj.
  
  Lemma proj_vtow : forall m k, vtow (proj m k) = projw m k. Proof. auto. Qed.

  (* Maybe name this pullback instead *)
  Definition jorp (mach:MachineState) (k:Component) (v:Value) : MachineState :=
    match k with
    | Reg r => update_reg mach r v
    | Mem m => update_mem mach m v
    | PC => update_reg mach addr_reg.PC v
    end.
  
  Parameter getComponents : MachineState -> list Component.
  
  (* Observations are ObsType, or silent (tau) *)
  Definition ObsType : Type := unit.
  
  Inductive Observation : Type := 
  | Out (o:ObsType) 
  | Tau. 

  Definition obs_eqb (o1 o2:Observation) : bool := true.

  (* A Machine State can step to a new Machine State plus an Observation. *)
  Fail
  Definition step' `{MachineParameters} (m:MachineState) : MachineState * Observation :=
    let '(rs,mem) := m in
    let pc := rs !r! addr_reg.PC in
    let a := match pc with
             | inl _ => top (* dummy *)
             | inr (_, _, _, _, a) => a
             end in
    let i := decodeInstrW (mem !m! a) in
    match exec i (rs, mem) with
    | (Executable, m') => (m',Tau)
    | _ => (m,Tau)
    end.

  Definition step (*`{MachineParameters}*) (m:MachineState) : MachineState * Observation.
  Proof.
    destruct m as [rs mem].
    set (pc := rs !r! addr_reg.PC).
    eset (a := match pc with
               | inl _ => top (* dummy *)
               | inr (_, _, _, _, a) => a
               end).
    set (i := decodeInstrW (mem !m! a)).
    exact (match exec i (rs, mem) with
           | (Executable, m') => (m',Tau)
           | _ => ((rs, mem),Tau)
           end).
    Unshelve.
    econstructor. instantiate (1 := 1). all:reflexivity.
  Defined.

  Definition FunID : Type := nat.
  Definition StackID : Type := nat.

  (*Definition EntryMap := Addr -> bool.*)

  Definition StackMap := Addr -> option StackID.

  Inductive CodeAnnotation : Type :=
  | call
  | retrn
  | yield
  | scall (f: MachineState -> Addr -> bool)
  | normal
  .

(*  Inductive CodeStatus :=
  | inFun   : FunID -> CodeAnnotation -> CodeStatus
  | notCode : CodeStatus
  .*)
  
  Definition CodeMap := Addr -> option CodeAnnotation.

  Definition activeStack (sm : StackMap) (m : MachineState) : option StackID :=
    match projw m (Reg SP) with
    | inl z => None
    | inr (_,_,ptr,_) => sm ptr
    end.
  
  Definition stack_eqb (sid1 sid2 : StackID) := sid1 =? sid2.

  Definition optstack_eqb (osid1 osid2 : option StackID) :=
    match osid1, osid2 with
    | Some sid1, Some sid2 => sid1 =? sid2
    | _, _ => false
    end.

  Definition justRet (mc m : MachineState) : Prop :=
    projw m PC = wplus (projw mc PC) 4 /\ projw m (Reg SP) = projw mc (Reg SP).

  Axiom justRet_dec : forall mc m, {justRet mc m} + {~ justRet mc m}.
  
End Cerise.
