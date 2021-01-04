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
Parameter w2nat : Word -> nat.

Parameter wplus_neq : forall w n, n > 0 -> w <> wplus w n.

Definition Addr : Type := Word.

Parameter Register : Type.
Parameter PC : Register.
Parameter SP : Register.
Parameter FP : Register.

Inductive Component:=
| Mem (a:Addr)
| Reg (r:Register).

Parameter keqb : Component -> Component -> bool.
Axiom keqb_implies_eq :
  forall k1 k2,
    keqb k1 k2 = true -> k1 = k2.
Axiom not_keqb_implies_neq :
  forall k1 k2,
    keqb k1 k2 = false -> k1 <> k2.

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
Parameter StackID : Type.

(*Definition Layout : Type := Addr -> bool.

Definition CallMap := Addr -> option Layout.

Definition RetMap := Addr -> Prop.

Parameter isRet : RetMap -> Addr -> bool.*)

Definition EntryMap := Addr -> Prop.

Definition CodeMap := Addr -> FunID -> Prop.

Parameter isCode : CodeMap -> Addr -> bool.

(*Definition YieldMap := Addr -> Prop.

Parameter isYield : YieldMap -> Addr -> bool.*)

Definition StackMap := Addr -> StackID -> Prop.

Parameter activeStack : StackMap -> MachineState -> StackID.
Parameter findStack : StackMap -> Addr -> option StackID.
Parameter sidEq : option StackID -> option StackID -> bool.

(*Definition ProgramMap := CallMap * RetMap * EntryMap * CodeMap * YieldMap * StackMap : Type.*)

Inductive CodeAnnotation :=
| call
| ret
| yield
| share (f: MachineState -> Addr -> option bool)
| normal
.

Inductive CodeStatus :=
| inFun : FunID -> CodeAnnotation -> CodeStatus
| notCode : CodeStatus
.

Definition CodeMap' := Addr -> CodeStatus.

Definition AnnotationOf (cdm : CodeMap') (a:Addr) : option CodeAnnotation :=
  match cdm a with
  | inFun f normal => None
  | inFun f ann => Some ann
  | notCode => None
  end.

Definition isCode' (cdm : CodeMap') (a:Addr) : bool :=
  match cdm a with
  | inFun _ _ => true
  | notCode => false
  end.

(*Definition isCall (cm: CallMap) (m: MachineState) (lay: Layout) : Prop :=
  cm (m (Reg PC)) = Some lay.*)

Definition justRet (mc m: MachineState) : Prop :=
  m (Reg PC) = wplus (mc (Reg PC)) 4 /\ m (Reg SP) = mc (Reg SP).

Definition justRet_dec mc m : {justRet mc m} + {~ justRet mc m}.
Proof.
  unfold justRet.
  destruct (WordEqDec (m (Reg PC)) (wplus (mc (Reg PC)) 4));
    destruct (WordEqDec (m (Reg SP)) (mc (Reg SP)));
    try solve [left; auto];
    right; intros [? ?]; auto.
Qed.

Parameter PolicyState : Type.
Parameter pstep : MachineState * PolicyState -> option PolicyState.
(* TODO: Does this ever fail? *)
(*Parameter initPolicyState : MachineState -> ProgramMap -> option PolicyState.*)

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
  Definition MPOTrace := MPTrace'.

  (* WithContour relates an MPTrace to its MCPTrace given an initial contour state cs.
     A finished trace (m,p) is related to (m,cs,p).
     We relate a trace (notfinished (m,p) MP) to (notfinished (m,cs,p) MCP),
     where MP relates to MCP given cs' produced by ContextStateUpdate. Additionally,
     the relation requires that MP begin with m' and p' produced by mpstep (m,p),
     so that only MPTraces produced by the step function relate to any MCPTrace *)
  Inductive WithContext (cs:ContextState) : MPTrace -> MCPTrace -> Prop :=
  | WCFinished : forall m p,
      WithContext cs (finished (m,p)) (finished (m,cs,p))
  | WCNotfinished : forall m p cs' m' p' o MP MCP,
      mpstep (m,p) = Some (m',p',o) ->
      ContextStateUpdate m cs = cs' ->
      WithContext cs' MP MCP ->
      head MP = (m',p') -> (* This checks that MP is actually real *)
      WithContext cs (notfinished (m,p) MP) (notfinished (m,cs,p) MCP).

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
End WITH_STATE.
