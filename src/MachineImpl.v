From StackSafety Require Import Trace Machine.

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
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Z.HexNotation.
Require coqutil.Map.SortedList.

Require Import Lia.

Module MachineImpl : MachineSpec.

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

(* A Machine State is just a map from Components to Values. *)

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
| share (f: MachineState -> Addr -> option bool)
| normal.

Inductive CodeStatus :=
| inFun   : FunID -> CodeAnnotation -> CodeStatus
| notCode : CodeStatus.

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

(*Definition isCall (cm: CallMap) (m: MachineState) (lay: Layout) : Prop :=
  cm (m (Reg PC)) = Some lay.*)

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
Definition PolicyState : Type := unit.
(* TODO: Does this ever fail? *)
(*Parameter initPolicyState : MachineState -> ProgramMap -> option PolicyState.*)

(* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
Definition MPState : Type := MachineState * PolicyState.
Definition ms (mp : MPState) := fst mp.
Definition ps (mp : MPState) := snd mp.

(* TODO: Real policy. *)
Definition mpstep (mp : MPState) : option (MPState * Observation) :=
  match step (ms mp) with
  | (m', o) => Some (m', tt, o)
  end.

Axiom mpstepCompat :
  forall m p o m' p',
    mpstep (m,p) = Some (m',p',o) ->
    step m = (m',o).

(* Confidentiality and Integrity Labels *)
Inductive CLabel :=
| HC
| LC.

Inductive ILabel :=
| HI
| LI.

Definition Label := (CLabel * ILabel)%type.

Definition Contour := Component -> Label.

Definition integrityOf (l : Label) : ILabel := snd l.
Definition confidentialityOf (l : Label) : CLabel := fst l.

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
  destruct (mpstep (m,p)); auto; destruct p0; auto.
Qed.

(* ******************* Trace stuff ********************* *)

(* We need to associate domainmaps with a trace. Here is some helpful machinery for associating
   states in general with a trace. *)
Section WITH_STATE.
  Variable ContextState : Type.
  Variable ContextStateUpdate : MachineState -> ContextState -> ContextState.
  
  Definition MCPState : Type := MachineState * ContextState * PolicyState.
  Definition MCPTrace := TraceOf MCPState.
  Definition mstate : MCPState -> MachineState := fun '(m,cs,p) => m.
  Definition cstate : MCPState -> ContextState := fun '(m,cs,p) => cs.
  Definition MCState : Type := MachineState * ContextState.
  Definition MCTrace := TraceOf MCState.
  Definition MPOTrace := MPTrace'.

  (* WithContour relates an MPTrace to its MCPTrace given an initial contour state cs.
     A finished trace (m,p) is related to (m,cs,p).
     We relate a trace (notfinished (m,p) MP) to (notfinished (m,cs,p) MCP),
     where MP relates to MCP given cs' produced by ContextStateUpdate. Additionally,
     the relation requires that MP begin with m' and p' produced by mpstep (m,p),
     so that only MPTraces produced by the step function relate to any MCPTrace *)
  Inductive WithContextMP (cs:ContextState) : MPTrace -> MCPTrace -> Prop :=
  | WCMPFinished : forall m p,
      WithContextMP cs (finished (m,p)) (finished (m,cs,p))
  | WCMPNotfinished : forall m p cs' m' p' o MP MCP,
      mpstep (m,p) = Some (m',p',o) ->
      ContextStateUpdate m cs = cs' ->
      WithContextMP cs' MP MCP ->
      head MP = (m',p') -> (* This checks that MP is actually real *)
      WithContextMP cs (notfinished (m,p) MP) (notfinished (m,cs,p) MCP).

  Inductive WithContextM (cs:ContextState) : MTrace -> MCTrace -> Prop :=
  | WCMFinished : forall m,
      WithContextM cs (finished m) (finished (m,cs))
  | WCMNotfinished : forall m cs' m' o MP MCP,
      step m = (m',o) ->
      ContextStateUpdate m cs = cs' ->
      WithContextM cs' MP MCP ->
      head MP = m' -> (* This checks that MP is actually real *)
      WithContextM cs (notfinished m MP) (notfinished (m,cs) MCP).

  (* Similarly, with WithObs we relate an MCPTrace into the MPOTrace
     corresponding to its steps annotated with their observations. We feed
     each step's observation forward, to line up with the machine state that follows that step.
     We will need this later. *)
  Inductive WithObs (o:Observation) : MCPTrace -> MPOTrace -> Prop :=
  | WOFinished : forall m c p,
      WithObs o (finished (m,c,p)) (finished (m,p,o))
  | WONotfinished : forall m c p m' c' o' p' MP MPO,
      WithObs o' MP MPO ->
      mpstep (m,p) = Some ((m',p'),o) ->
      head MP = (m',c',p') ->
      WithObs o (notfinished (m,c,p) MP) (notfinished (m,p,o) MPO).
  
  (* ObsOfMCP starts the observation with Tau, reflecting that initially
     there is no observation until a step occurs. *)
  Definition ObsOfMCP := WithObs Tau.

  Inductive WithObsM (o:Observation) : MCTrace -> TraceOf (MachineState*Observation) -> Prop :=
  | WOMFinished : forall m c,
      WithObsM o (finished (m,c)) (finished (m,o))
  | WOMNotfinished : forall m c m' c' o' M MO,
      WithObsM o' M MO ->
      step m = (m',o) ->
      head M = (m',c') ->
      WithObsM o (notfinished (m,c) M) (notfinished (m,o) MO).
  
  (* ObsOfMCP starts the observation with Tau, reflecting that initially
     there is no observation until a step occurs. *)
  Definition ObsOfMC := WithObsM Tau.

  (* ContextSegment relates two MCPTraces given a condition f on machine and context states,
     where the second is a longest subtrace of the first such that f holds on all elements
     except the final. So, it will always have at least two elements, and its head will have been
     preceded by one on which f does not hold, while the last (if any) also does not have f hold.
     
     We will use this machinery to clip out sections of a trace that we want to check
     against a property, with the final state reflecting the state after some relevant execution.
   *)
  Inductive ContextSegment (f : MachineState -> ContextState -> Prop) : MCPTrace -> MCPTrace -> Prop :=
  | CSCurrent : forall MCP MCP' m cs p,
      head MCP = (m,cs,p) ->
      f m cs ->
      PrefixUpTo (fun '(m,cs,p) => ~ f m cs) MCP MCP' ->
      ContextSegment f (notfinished (m,cs,p) MCP) (notfinished (m,cs,p) MCP')
  | CSNot : forall MCP MCPpre MCPsuff MCP' m cs p,
      head MCP = (m,cs,p) ->
      ~ f m cs ->
        SplitInclusive (fun '(m,cs,p) => f m cs) MCP MCPpre MCPsuff ->
        ContextSegment f MCPsuff MCP' ->
        ContextSegment f MCP MCP'
  | CSSkip : forall MCP MCPpre MCPsuff MCP' m cs p,
      head MCP = (m,cs,p) ->
      f m cs ->
      SplitInclusive (fun '(m,cs,p) => f m cs) MCP MCPpre MCPsuff ->
      ContextSegment f MCPsuff MCP' ->
      ContextSegment f MCP MCP'
  .

  Inductive ContextSegmentM (f : MachineState -> ContextState -> Prop) : MCTrace -> MCTrace -> Prop :=
  | CSMCurrent : forall MC MC' m cs,
      head MC = (m,cs) ->
      f m cs ->
      PrefixUpTo (fun '(m,cs) => ~ f m cs) MC MC' ->
      ContextSegmentM f (notfinished (m,cs) MC) (notfinished (m,cs) MC')
  | CSMNot : forall MC MCpre MCsuff MC' m cs,
      head MC = (m,cs) ->
      ~ f m cs ->
      SplitInclusive (fun '(m,cs) => f m cs) MC MCpre MCsuff ->
      ContextSegmentM f MCsuff MC' ->
      ContextSegmentM f MC MC'
  | CSMSkip : forall MC MCpre MCsuff MC' m cs,
      head MC = (m,cs) ->
      f m cs ->
      SplitInclusive (fun '(m,cs) => f m cs) MC MCpre MCsuff ->
      ContextSegmentM f MCsuff MC' ->
      ContextSegmentM f MC MC'
  .

End WITH_STATE.

Arguments WithContextMP {_}  _ _ _ _.
Arguments WithContextM {_}  _ _ _ _.
Arguments ContextSegment {_} _ _ _.
Arguments ContextSegmentM {_} _ _ _.
Arguments ObsOfMCP {_}.
Arguments ObsOfMC {_}.
Arguments MCPState {_}.
Arguments MCPTrace {_}.
Arguments cstate {_}.
Arguments mstate {_}.


End MachineImpl.
