Require Import Coq.Lists.List.
Import List.ListNotations.

From StackSafety Require Import Trace.

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

  Definition Word := MachineInt.
  (* Parameter Word *)

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

  (* Observations are values, or silent (tau) *)
  Inductive Observation : Type := 
  | Out (w:Value) 
  | Tau. 

  (* A Machine State can step to a new Machine State plus an Observation. *)
  Definition step (m : RiscvMachine) : RiscvMachine * Observation :=
    (* returns option unit * state *)
    (* TODO: What's an observation? *)
    match Run.run1 RV32IM m with
    | (_, s') => (s', Tau)
    end
  .

  Definition FunID := nat.
  Definition StackID := nat.

  Definition EntryMap := Addr -> bool.

  Definition StackMap := Addr -> option StackID.

  Inductive CodeAnnotation :=
  | call
  | ret
  | yield
  | scall (f: MachineState -> Addr -> bool)
  | normal
  .

  Inductive CodeStatus :=
  | inFun   : FunID -> CodeAnnotation -> CodeStatus
  | notCode : CodeStatus
  .
  
  Definition CodeMap := Addr -> CodeStatus.

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

  Definition AnnotationOf (cdm : CodeMap) (a:Addr) : option CodeAnnotation :=
    match cdm a with
    | inFun f normal => None
    | inFun f ann => Some ann
    | notCode => None
    end.

  Definition isCode' (cdm : CodeMap) (a:Addr) : bool :=
    match cdm a with
    | inFun _ _ => true
    | notCode => false
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

(* TODO: More interesting state/abstract *)
Inductive Tag : Type :=
| Tcall
| Th1
| Th2
| Tinstr
| Tpc (n : nat)
| Tr1
| Tr2
| Tr3
| Tsp
| Tstack (n : nat)
.

Definition tag_eqb (t1 t2 :  Tag) : bool :=
  match t1, t2 with
  | Tcall, Tcall
  | Th1, Th1
  | Th2, Th2
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
Definition TagMap : Type := Zkeyed_map TagSet.

(* Map of memory tags *)
Record PolicyState : Type :=
  {
  nextid: nat;
  pctags: TagSet;
  regtags: TagMap;
  memtags: TagMap;
  }.

Instance etaPolicyState : Settable _ :=
  settable! Build_PolicyState <nextid; pctags; regtags; memtags>.

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
  | [Tinstr; Th2] =>
    match existsb (tag_eqb Th2) tpc, trs with
    | true, [Tsp] => Some (p <| pctags := filter (tag_neqb Th2) tpc |>
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
    match tpc, existsb (tag_eqb Tsp) taddr, trs, existsb (tag_eqb Tinstr) tmem with
    | [Tpc depth], (*false*)_, [], false => Some (p <| memtags := map.put (memtags p) addr [Tstack depth] |>)
    | _, _, _, _ => None
    end
  | [Tinstr; Th1] =>
    match existsb (tag_eqb Th1) tpc, trs, taddr with
    | true, [Tpc depth], [Tsp] => Some (p <| pctags := filter (tag_neqb Th1) tpc ++ [Th2] |>
                                          <| memtags := map.put (memtags p) addr [Tpc depth] |>)
    | _, _, _ => None
    end
  | _ => None
  end.

Definition decodeI (w : w32) : option InstructionI :=
  match decode RV32IM (LittleEndian.combine 4 w) with
  | IInstruction i => Some i
  | _ => None
  end.

Definition pstep (mp : MPState) : option PolicyState :=
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
  end.

Definition mpstep (mp : MPState) : option (MPState * Observation) :=
  p' <- pstep mp;
  match step (ms mp) with
  | (m', o) => Some (m', p', o)
  end
.

Axiom mpstepCompat :
  forall m p o m' p',
    mpstep (m,p) = Some (m',p',o) ->
    step m = (m',o).

(* TODO: More interesting well-formedness condition *)
Definition WFInitMPState (mp:MPState) := True.

(********* Steps and Traces ***********)

Definition MTrace := TraceOf MachineState.

CoFixpoint MTraceOf (M : MachineState) : MTrace :=
  notfinished M (MTraceOf (fst (step M))).

Definition MPTrace := TraceOf MPState.

CoFixpoint MPTraceOf (mp : MPState) : MPTrace :=
  match mpstep mp with
  | None => finished mp
  | Some (mp',o) => notfinished mp (MPTraceOf mp')
  end.

Definition MTrace' := TraceOf (MachineState * Observation).

CoFixpoint RunOf (m : MachineState) : MTrace' :=
  notfinished (m,snd (step m)) (RunOf (fst (step m))).

Definition MPTrace' := TraceOf (MachineState * PolicyState * Observation).

CoFixpoint MPRunOf (mp : MPState) : MPTrace' :=
  match mpstep mp with
  | None =>
    finished (mp,Tau)
  | Some (mp',o) =>
    notfinished (mp,o) (MPRunOf mp')
  end.

(********** Machine Lemmas ************)
Lemma MTraceOfInf :
  forall m,
    infinite (MTraceOf m).
Proof.  
  intros m m' H.
  remember (MTraceOf m) as M.
  generalize dependent m.
  induction H; intros m HeqM.
  - rewrite (idTrace_eq (MTraceOf m)) in HeqM.
    simpl in *.
    inversion HeqM.
  - rewrite (idTrace_eq (MTraceOf m)) in HeqM.
    simpl in *.
    inversion HeqM; subst; clear HeqM.
    eapply IHLast; eauto.
Qed.

Lemma MPTraceOfHead: forall mp, mp = head (MPTraceOf mp).
Proof.
  intros. destruct mp.  simpl. 
  (* destruct (mpstep (m,p)); auto; destruct p0; auto. *)
(* Qed. *)
Abort. (* FIXME *)

(* ******************* Trace stuff ********************* *)

Section WITH_STATE.
  Variable CtxState : Type.
  Variable CtxStateUpdate : MachineState -> CtxState -> CtxState.
  Variable initCtx : MachineState -> CtxState.
  
  Definition MPCState : Type := MachineState * PolicyState * CtxState.
  Definition MPCTrace := TraceOf MPCState.
  Definition mstate : MPCState -> MachineState := fun '(m,p,cs) => m.
  Definition pstate : MPCState -> PolicyState := fun '(m,p,cs) => p.
  Definition cstate : MPCState -> CtxState := fun '(m,p,cs) => cs.

  Definition mpcstep (mpc:MPCState) : option (MPCState * Observation) :=
    option_map
      (fun '(m,p,o) => (m,p,CtxStateUpdate m (cstate mpc),o))
      (mpstep (mstate mpc,pstate mpc)).
  
  Inductive StepsTo : MPCState -> MPCState -> Prop :=
  | already : forall mpc, StepsTo mpc mpc
  | future : forall mpc mpc' mpc'' o,
      StepsTo mpc mpc' ->
      mpcstep mpc' = Some (mpc'',o) ->
      StepsTo mpc mpc''.

  Inductive StepsToWhenObs (P:MPCState -> Prop) : MPCState -> MPCState -> TraceOf Observation -> Prop :=
  | when : forall mpc,
      P mpc ->
      StepsToWhenObs P mpc mpc (finished Tau)
  | futureWhen : forall mpc mpc' mpc'' o O,
      ~ P mpc ->
      mpcstep mpc = Some (mpc',o) ->
      StepsToWhenObs P mpc' mpc'' O ->
      StepsToWhenObs P mpc mpc'' (notfinished o O).

  Definition StepsToWhen P mpc mpc' := exists O, StepsToWhenObs P mpc mpc' O.

  Inductive FullObsTrace : MPCState -> TraceOf Observation -> Prop :=
  | stepIt : forall mpc mpc' o O,
      mpcstep mpc = Some (mpc',o) ->
      FullObsTrace mpc' O ->
      FullObsTrace mpc (notfinished o O).

  Definition NeverStepsToObs P mpc O :=
    FullObsTrace mpc O /\
    forall mpc',
      ~ StepsToWhen P mpc mpc'.

  Definition Reachable (mpc:MPCState) : Prop :=
    exists mpinit,
      WFInitMPState mpinit /\ StepsTo (mpinit,initCtx (fst mpinit)) mpc.

  CoFixpoint MPCTraceOf (mpc : MPCState) : MPCTrace :=
    match mpcstep mpc with
    | None => finished mpc
    | Some (mpc',o) => notfinished mpc (MPCTraceOf mpc')
    end.

  CoInductive MPCTraceToWhen (P:MPCState -> Prop) : MPCState -> MPCTrace -> Prop :=
  | TTWNow : forall mpc,
      P mpc ->
      MPCTraceToWhen P mpc (finished mpc)
  | TTWNever : forall mpc,
      mpcstep mpc = None ->
      MPCTraceToWhen P mpc (finished mpc)
  | TTWLater : forall mpc mpc' o MPC,
      ~ P mpc ->
      mpcstep mpc = Some (mpc',o) ->
      MPCTraceToWhen P mpc' MPC ->
      MPCTraceToWhen P mpc (notfinished mpc MPC)
  .
  
  (* Similarly, with WithObs we relate an MCPTrace into the MPOTrace
     corresponding to its steps annotated with their observations. We feed
     each step's observation forward, to line up with the machine state that follows that step.
     We will need this later. *)
  Inductive WithObs (o:Observation) : MPCTrace -> TraceOf Observation -> Prop :=
  | WOFinished : forall mpc,
      WithObs o (finished mpc) (finished o)
  | WONotfinished : forall mpc mpc' o' MPC O,
      WithObs o' MPC O ->
      mpcstep mpc = Some (mpc',o') ->
      WithObs o (notfinished mpc MPC) (notfinished o O).
  
  (* ObsOfMCP starts the observation with Tau, reflecting that initially
     there is no observation until a step occurs. *)
  Definition ObsOfMPC := WithObs Tau.
  
  Inductive Segment (f : MPCState -> Prop) : MPCTrace -> MPCTrace -> Prop :=
  | SegCurrent : forall MPC MPC' mpc,
      f mpc ->
      PrefixUpTo (fun mpc' => ~ f mpc') MPC MPC' ->
      Segment f (notfinished mpc MPC) (notfinished mpc MPC')
  | SegNot : forall MPC MPCpre MPCsuff MPC' mpc,
      ~ f mpc ->
      SplitInclusive f MPC MPCpre MPCsuff ->
      Segment f MPCsuff MPC' ->
      Segment f (notfinished mpc MPC) MPC'
  | SegSkip : forall MPC MPCpre MPCsuff MPC' mpc,
      f mpc ->
      SplitInclusive f MPC MPCpre MPCsuff ->
      Segment f MPCsuff MPC' ->
      Segment f (notfinished mpc MPC) MPC'
  .

  Definition ReachableSegment (f : MPCState -> Prop) (MPC:MPCTrace) : Prop :=
    exists mpinit,
      WFInitMPState mpinit /\ Segment f (MPCTraceOf (mpinit,initCtx (fst mpinit))) MPC.

  Lemma ReachableStepsToWhenSegment :
    forall mpc mpc' P,
      Reachable mpc ->
      StepsToWhen P mpc mpc' ->
      exists MPC,
        ReachableSegment P MPC /\
        head MPC = mpc /\
        Last MPC mpc'.
  Proof.
  Admitted.
(*    intros. destruct H0 as [O]. induction H0.
    - exists (finished mpc).
      split.
      + unfold ReachableSegment.
        unfold Reachable in H.
        destruct H as [mpinit]; exists mpinit.
        destruct H. split; auto. *)
        

End WITH_STATE.

Arguments Segment {_} _ _ _.
Arguments ObsOfMPC {_}.
Arguments MPCState {_}.
Arguments MPCTrace {_}.
Arguments cstate {_}.
Arguments mstate {_}.
Arguments pstate {_}.
Arguments Reachable {_} _ _ _.
Arguments mpcstep {_} _ _.
Arguments MPCTraceOf {_} _.
Arguments MPCTraceToWhen {_} _ _ _.
Arguments StepsToWhenObs {_} _ _ _ _.
Arguments StepsToWhen {_} _ _ _.
Arguments ReachableSegment {_} _ _ _.
Arguments NeverStepsToObs {_} _ _ _.

