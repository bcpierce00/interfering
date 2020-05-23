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

Definition CallMap := Value -> nat -> Prop.

Definition isCall (cm: CallMap) (m: MachineState) (args: nat) : Prop :=
   cm (m (Reg PC)) args.

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
