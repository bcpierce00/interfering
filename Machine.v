Require Import Trace.

(* Primitive Abstraction. *)

Parameter Word : Type. 
Parameter wlt : Word -> Word -> bool.
Parameter weq : Word -> Word -> bool.
Axiom WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.
Axiom weq_implies_eq :
  forall w1 w2,
    weq w1 w2 = true -> w1 = w2.
Axiom not_weq_implies_neq :
  forall w1 w2,
    weq w1 w2 = false -> w1 <> w2.
Definition wle (w1 w2: Word) : bool := orb (wlt w1 w2) (weq w1 w2).
Parameter wplus : Word -> nat -> Word.
Parameter wminus : Word -> nat -> Word.

Parameter wplus_neq : forall w n, n > 0 -> w <> wplus w n.

Definition Addr : Type := Word.

Parameter Register : Type.
Parameter PC : Register.
Parameter SP : Register.

Inductive Component:=
| Mem (a:Addr)
| Reg (r:Register).

(* A Value is a Word. *)
Definition Value : Type := Word.

(* A Machine State is just a map from Components to Values. *)
Definition MachineState := Component -> Value.

(* Observations are values, or silent (tau) *)
Inductive Observation : Type := 
| Out (w:Value) 
| Tau. 

(* A Machine State can step to a new Machine State plus an Observation. *)
Parameter step : MachineState -> MachineState * Observation.

Parameter FunID : Type.

Definition CallMap := Value -> option nat.

Definition RetMap := Value -> Prop.

Definition OwnerMap := Value -> FunID -> Prop.

Definition isCall (cm: CallMap) (m: MachineState) (args: nat) : Prop :=
   cm (m (Reg PC)) = Some args.

Definition isRet (mc m: MachineState) : Prop :=
  m (Reg PC) = wplus (mc (Reg PC)) 4 /\ m (Reg SP) = mc (Reg SP).

Definition isRet_dec mc m : {isRet mc m} + {~ isRet mc m}.
Proof.
  unfold isRet.
  destruct (WordEqDec (m (Reg PC)) (wplus (mc (Reg PC)) 4));
    destruct (WordEqDec (m (Reg SP)) (mc (Reg SP)));
    try solve [left; auto];
    right; intros [? ?]; auto.
Qed.

Parameter PolicyState : Type.
Parameter pstep : MachineState * PolicyState -> option PolicyState.
(* TODO: Does this ever fail? *)
Parameter initPolicyState : MachineState -> CallMap -> PolicyState.

(* TODO: Rename MPState to State and MPTrace to Trace, mp -> t *)
Definition MPState : Type := MachineState * PolicyState.
Definition ms (mp : MPState) := fst mp.
Definition ps (mp : MPState) := snd mp.

Definition mpstep (mp : MPState) :=
  let (m', O) := step (ms mp) in
  match pstep mp with
  | Some p' => Some (m', p', O)
  | None => None
  end.

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
  match pstep mp with
  | None => finished mp
  | Some p' => notfinished mp (MPTraceOf (fst (step (ms mp)), p'))
  end.

Definition MTrace' := TraceOf (MachineState * Observation).

CoFixpoint RunOf (m : MachineState) : MTrace' :=
  notfinished (m,snd (step m)) (RunOf (fst (step m))).

Definition MPTrace' := TraceOf (MachineState * PolicyState * Observation).

CoFixpoint MPRunOf (mp : MPState) : MPTrace' :=
  match pstep mp with
  | None =>
    finished (mp,Tau)
  | Some p' =>
    notfinished (mp,snd (step (ms mp))) (MPRunOf (fst (step (ms mp)), p'))
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
  destruct (pstep (m,p)); auto.
Qed.
