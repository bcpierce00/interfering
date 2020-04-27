Require Import List.
Import ListNotations.

Section foo.

(* TODO: Make all this match the terminology in the .tex -- e.g., a
   Contour should correspond to a MachineState, not to a Trace,
   etc. *)

  Variable Word : Type.
  Variable Register : Type.

  Definition Addr : Type := Word.
  Definition Value : Type := Word.

  Inductive Component:=
  | Mem (a:Addr)
  | Reg (r:Register).

          
  Definition MachineState := Component -> Value.

(* APT: Since Components include registers, these aren't total orders, which is confusing. 
        Maybe we should get more honest about the makeup of Components?
        Or : just do these comparisons on Values; then we don't really need componentOf. *)
(* LEO: Components/Values: I agree that the abstraction we have right
now is iffy. There should be components (registers, pc, pointers) and
values (words). You can extract the value of a component given a
machine state (always I think?).  We also need to compare components
however: A contour is a map from components to labels, and during a
call we change that mapping depending on whether the component lies in
a particular position with respect to the SP.  We could have a
"withinRegion" function that only returns true if it is a valid
(stack) pointer with two other component-pointers. If we wanted to do
the ordering at the value level, then we would need a different
Component -> Value function "asValue", that reads of the "address" of
the component (and then this induces an ordering in components
itself). Not sure what the cleanest abstraction is here. *)

(* BCP: To me it seems cleaner to keep the distinction between
components and values.  I’ve been wondering whether we need to
explicitly recognize that there is a stack (i.e., whether we need,
say, an ordering on components). *)

(* APT: The Coq development currently has an ordering on components.
The problem is that it is total, so needs to be defined on registers
as well as stack addresses. 
A fairly simple way to fix this is just to make the order partial.   
A clearer way might be to do what is in the latex and define 
 Component = Addr + Register 
 Addr = Word 
 Value = Word 
and then just put an order on Word. *)

  Variable wlt : Word -> Word -> bool.
  Variable weq : Word -> Word -> bool.
  Definition wle (w1 w2: Word) : bool := orb (wlt w1 w2) (weq w1 w2).

(*
Variable clt : Component -> Component -> bool.
Variable cle : Component -> Component -> bool.
 *)
  
Variable PC : Register.
Variable SP : Register.
(* SNA: we should consider weaker forms of observability, like a special output register. *)
Variable O : Register.

(*Variable Value : Type. *)
(* Definition valueOf (C:Component) (M:MachineState) : Value := M C. *)
(* Variable veq : Value -> Value -> bool. *)

(* Should this be option? *)
(* APT: See above. *)
(* Variable componentOf : Value -> option Component. *)

(* Variable initSP : Value. *)
Variable JAL : Word.
Variable incr : Word -> Word. 
Variable wplus : Word -> nat -> Word. 
Variable wminus : Word -> nat -> Word. 

Variable step : MachineState -> option MachineState.

(* TODO: Change these *)
Inductive CLabel :=
| HC
| LC.

Inductive ILabel :=
| HI
| LI.

Definition Label := (CLabel * ILabel)%type.

Definition Contour := Component -> Label.

CoInductive Trace (A : Type) : Type :=
| finished : A -> Trace A
| notfinished : A -> Trace A -> Trace A.

Arguments finished {_} _.
Arguments notfinished {_} _ _.

(* Definition idTrace {A} (MM: Trace A) : Trace A := *)
(*   match MM with *)
(*   | finished M => finished M *)
(*   | notfinished M MM' => notfinished M  MM' *)
(*   end. *)

(* Lemma idTrace_eq : forall {A} (MM: Trace A), MM = idTrace MM. *)
(*   destruct MM; reflexivity. *)
(* Qed. *)


Definition head {A} (MM : Trace A) : A :=
  match MM with
  | finished M => M
  | notfinished M _ => M
  end.

Inductive InTrace {A} (m:A) : Trace A -> Prop :=
| In_finished : InTrace m (finished m)
| In_now : forall MM, InTrace m (notfinished m MM)                        
| In_later : forall m' MM, InTrace m MM -> InTrace m (notfinished m' MM).

Lemma head_InTrace :forall {A} (MM: Trace A), InTrace (head MM) MM.
Proof.
  intros.
  destruct MM. 
  - constructor.
  - simpl. constructor.
Qed.

CoFixpoint mapTrace {A B:Type} (f:A -> B) (MM: Trace A) : Trace B :=
  match MM with
  | finished M => finished (f M)
  | notfinished M MM' => notfinished (f M) (mapTrace f MM')
  end.

CoInductive ForallTrace {A:Type} (P:A -> Prop) : Trace A -> Prop :=
| Forall_finished : forall M, P M -> ForallTrace P (finished M)
| Forall_notfinished : forall M MM', P M -> ForallTrace P MM' -> ForallTrace P (notfinished M MM')
.

(* Definition tail {A} (MM: Trace A) : option (Trace A) := *)
(*   match MM with *)
(*   | finished _ => None *)
(*   | notfinished _ M => Some M *)
(*   end. *)
  
(* Fixpoint ith {A} (i:nat) (MM: Trace A) : option A := *)
(*   match i with *)
(*   | O => Some (head MM) *)
(*   | S i' => match tail MM with *)
(*             | Some MM' => ith i' MM' *)
(*             | None => None                               *)
(*             end *)
(*   end. *)

(* Lemma head_ith : forall {A} (MM: Trace A), ith O MM = Some (head MM). *)
(* Proof. *)
(*   destruct MM. *)
(*   - auto. *)
(*   - auto. *)
(* Qed. *)

Definition MTrace := Trace MachineState.

CoFixpoint traceOf (M : MachineState) : MTrace :=
  match step M with
  | None => finished M
  | Some M' => notfinished M (traceOf M')
  end.

Definition integrityOf (l : Label) : ILabel := snd l.
Definition confidentialityOf (l : Label) : CLabel := fst l.

CoInductive StackIntegrity (C : Contour) : MTrace -> Prop :=
| SI_finished : forall M, StackIntegrity C (finished M)
| SI_notfinished :
    forall (M0: MachineState) (MM: MTrace),
    (forall (k: Component), integrityOf (C k) = HI ->
                            M0 k = (head MM) k) ->
    StackIntegrity C MM ->
    StackIntegrity C (notfinished M0 MM).


(* APT: An equivalent alternative definition that more closely matches the latex... *)

Definition StackIntegrity' (C : Contour) (MM: MTrace) : Prop :=
    forall (k: Component), integrityOf (C k) = HI ->
      forall (m: MachineState), InTrace m MM -> (head MM) k = m k.

Lemma StackIntegrityEquiv : forall (C:Contour) (MM: MTrace),
     StackIntegrity' C MM -> StackIntegrity C MM.
Proof.
  cofix COFIX.
  intros.
  destruct MM. 
  - constructor.
  - constructor.
    + intros. unfold StackIntegrity' in H.  simpl in H. 
      apply H; auto. constructor. apply head_InTrace. 
    + apply COFIX. 
      unfold StackIntegrity' in *.  intros. simpl in H. 
      erewrite <- H; auto. 
      * apply H; auto.  constructor. auto.
      * constructor. apply head_InTrace.
Qed.

Lemma StackIntegrity'Equiv : forall (C:Contour) (MM: MTrace),
     StackIntegrity C MM -> StackIntegrity' C MM.
Proof.
  intros.
  unfold StackIntegrity'. 
  intros.
  induction H1. 
  - auto.
  - auto.
  - simpl. inversion H. subst. rewrite <- IHInTrace.
    +  apply H4; auto. 
    +  inversion H.  auto.
Qed.

Definition variantOf (M N : MachineState) (C : Contour) :=
  forall (k : Component), confidentialityOf (C k) = LC ->
                          M k = N k.

Definition Obs (M : MachineState) := M (Reg O).

Definition ObsTrace := Trace Value.

(* Stuttering version *)
Definition ObsTraceOf' (MM : MTrace) := mapTrace Obs MM.

(* SNA: alternative obs: non-stuttering trace of output register *)
CoFixpoint ObsTraceOf (MM : MTrace) : Trace Value :=
  match MM with
  | finished M =>
    finished (M (Reg O))
  | notfinished M Ms =>
    let v := M (Reg O) in 
    match Ms with
    | finished M' =>
      let v' := M' (Reg O) in 
      if weq v v'
      then finished v
      else notfinished v (finished v')
    | notfinished M' Ms' =>
      let v' := M' (Reg O) in
      if weq v v'
      then notfinished v (ObsTraceOf Ms')
      else notfinished v (ObsTraceOf (notfinished M' Ms'))
    end
  end.

(* APT: TODO: Show that Leo's original version of ObsTrace equivalence implies lock-step equivalence. *)

CoFixpoint TraceApp {A} (MM: Trace A) (MMO: option (Trace A)) : Trace A :=
  match MM with
  | finished m =>
    match MMO with
    | Some m' => notfinished m m'
    | None => MM
    end
  | notfinished m MM' => notfinished m (TraceApp MM' MMO)
  end.

Definition OptTraceApp {A} (MMO1: option (Trace A)) (MMO2: option (Trace A)) : option (Trace A) :=
  match MMO1 with
  | Some MM => Some (TraceApp MM MMO2)
  | None => MMO2
  end.

CoInductive TracePrefix {A} : Trace A -> Trace A -> Prop :=
| PrefixEq  : forall m, TracePrefix (finished m) (finished m)
| PrefixNow : forall m mm, TracePrefix (finished m) (notfinished m mm)
| PrefixLater : forall m mm1 mm2, TracePrefix mm1 mm2 ->
                                  TracePrefix (notfinished m mm1)
                                              (notfinished m mm2).

CoInductive TraceEq {A} : Trace A -> Trace A -> Prop :=
| EqFin : forall m, TraceEq (finished m) (finished m)
| EqCons : forall m mm1 mm2, TraceEq mm1 mm2 ->
                             TraceEq (notfinished m mm1) (notfinished m mm2).

Definition TraceSpan {A} (P : A -> Prop) (MM1 MM2 : Trace A) (MMO : option (Trace A)) : Prop :=
  MM1 = TraceApp MM2 MMO /\ ForallTrace P MM2 /\
  forall MM2', TracePrefix MM2' MM1 ->
    ForallTrace P MM2' ->
    TracePrefix MM2' MM2.

Definition LongestPrefix {A} (MM1 MM2 : Trace A) (P : A -> Prop) : Prop :=
  TracePrefix MM2 MM1 /\ ForallTrace P MM2 /\
  forall MM2', TracePrefix MM2' MM1 ->
    ForallTrace P MM2' ->
    TracePrefix MM2' MM2.

Definition StackConfidentiality (C : Contour) (MM : MTrace) := 
  forall N, variantOf (head MM) N C ->
            let o  := ObsTraceOf MM in
            let o' := ObsTraceOf (traceOf N) in
            TracePrefix o o'. (* \/ TracePrefix o' o) *)

(* APT: just this direction: it would be bad if variant trace ended sooner than reference, right? *)
(* LEO: I'm not sure about only one observation being a prefix of the other. What if the variant machine tries halts because of the monitor? Are we termination-sensitive? *)
(* APT: Ah, right.  I guess we have to be termination-insensitive. *)
(* APT+SEAN: On third thought, we're not sure we buy this. Why should the variant be allowed 
to fail-stop more often than the reference trace? *)

Definition CallMap := Value -> nat -> Prop. 

Definition isCall (cm: CallMap) (M: MachineState) (iaddr: Value) (args: nat) : Prop :=
  M (Reg PC) = iaddr /\ cm iaddr args.

Definition isRet (Mc M: MachineState) : Prop :=
  M (Reg PC) = wplus (Mc (Reg PC)) 4 /\ M (Reg SP) = Mc (Reg SP).

Definition updateContour (C: Contour) (args: nat) (M: MachineState) : Contour :=
  fun k =>
    match k with
    | Mem a => 
      let a' := wminus (M (Reg SP)) args in
      if wle a a' then
        (HC, HI)
      else if andb (wlt a' a) (wle a (M (Reg SP))) then
        (LC, LI)                  
      else if wlt (M (Reg SP)) a then
        (HC, LI)
      else C k
    | _ => C k
    end.

CoInductive Subtrace : Contour -> MTrace -> Contour -> MTrace -> Prop :=
  | SubNow : forall iaddr args cm C C' MM MM',
      (* Current instruction is a call *)
      isCall cm (head MM) iaddr args ->
      (* Take the prefix until a return *)
      (* APT/SNA: Does this want to be LongestPrefix ? *)
      TracePrefix MM' MM ->
      ForallTrace (fun M => ~ (isRet (head MM) M)) MM' ->
      (* Construct the new contour *)
      updateContour C args (head MM) = C' -> 
      Subtrace C MM C' MM'
  | SubLater : forall C MM C' MM' M,
      Subtrace C MM C' MM' ->
      Subtrace C (notfinished M MM) C' MM'.

CoInductive StackSafety (cm : CallMap) : MTrace -> Contour -> Prop :=
  ss : forall (MM : MTrace) (C : Contour),
       (StackIntegrity C MM) ->
       (StackConfidentiality C MM) ->
       (forall MM' C', Subtrace C MM C' MM' -> StackSafety cm MM' C') ->
       StackSafety cm MM C.

(* ********* SNA Beware : Lazy Properties ********* *)

(* this variation of subtrace also gives us the suffix of the primary trace
   after the subtrace, or None if the subtrace is itself a suffix *)
CoInductive SubtraceWithSuffix : Contour -> MTrace -> Contour -> MTrace -> option MTrace -> Prop :=
  | SubSufNow : forall iaddr args cm C C' MM MM' MMO,
      (* Current instruction is a call *)
      isCall cm (head MM) iaddr args ->
      (* Take the prefix until a return -- the entire thing *)
      TraceSpan (fun M => ~ (isRet (head MM) M)) MM MM' MMO ->
      (* Construct the new contour *)
      updateContour C args (head MM) = C' ->
      SubtraceWithSuffix C MM C' MM' MMO
  | SubSufLater : forall C MM C' MM' M MMO,
      SubtraceWithSuffix C MM C' MM' MMO ->
      SubtraceWithSuffix C (notfinished M MM) C' MM' MMO.

(* These helpers just tell us when one field is higher in the second argument than the first. *)
Definition wentUpInt (outer inner : Label) : bool :=
  match outer, inner with
  | (_,LI), (_,HI) => true
  | _, _ => false
  end.

Definition wentUpConf (outer inner : Label) : bool :=
  match outer, inner with
  | (LC,_), (HC,_) => true
  | _, _ => false
  end.

Definition wentUp (outer inner : Label) : bool :=
  match outer, inner with
  | (LC,_), (HC,_) => true
  | (_,LI), (_,HI) => true
  | _, _ => false
  end.

(* A rollback takes an initial state and a final state and their inner and outer contours,
   and gives a state in which those components that went up between contours are restored
   to their initial values, and all other components respect their final values. *)
Definition RollbackInt (C C': Contour) (Mstart Mend : MachineState) : MachineState :=
  fun k => (if wentUpInt (C k) (C' k) then Mstart else Mend) k.

Definition RollbackConf (C C': Contour) (Mstart Mend : MachineState) : MachineState :=
  fun k => (if wentUpConf (C k) (C' k) then Mstart else Mend) k.

Definition Rollback (C C': Contour) (Mstart Mend : MachineState) : MachineState :=
  fun k => (if wentUp (C k) (C' k) then Mstart else Mend) k.

(* Observable properties are relations on a contour and reference trace at that contour,
   with an additional trace of the remaining execution after the current contour. *)
CoInductive ObservableIntegrity : Contour -> MTrace -> option MTrace -> Prop :=
  | safetrace : forall C MM MMOrest,
                  (* for any subtrace of MM and its suffix, if any *)
                  (forall MMsub MMO MMsuf MMsuf' C',
                    SubtraceWithSuffix C MM C' MMsub MMO ->
                    (MMO = Some MMsuf ->
                      MMsuf' = traceOf (RollbackInt C C' (head MMsub) (head MMsuf)) ->
                      (* and check if observable behavior of the reference prefixes
                         that of the rollback (prefix because lazy policies might failstop
                         reference trace but not rollback trace) *)
                      TracePrefix (ObsTraceOf (TraceApp MMsuf MMOrest)) (ObsTraceOf MMsuf')) ->
                    (* inside each subtrace, do the same, passing suffix in as remaining execution *)
                    ObservableIntegrity C' MMsub (OptTraceApp MMO MMOrest)) ->
                  ObservableIntegrity C MM MMOrest.

CoInductive ObservableConfidentiality : Contour -> MTrace -> option MTrace -> Prop :=
| varytrace' : forall C MM MMOrest,
                  (forall MMsub MMO MMext NN NNO NNext C' N,
                    SubtraceWithSuffix C MM C' MMsub MMO ->
                    (* this time we vary the state at call and run until return *)
                    variantOf (head MMsub) N C' ->
                    TraceSpan (fun M => ~ (isRet (head MM) M)) (traceOf N) NN NNO ->
                    MMext = TraceApp MMsub MMO ->
                    (* if varied trace returns, varied memory must be rolled back before continuing *)
                    NNext = TraceApp NN (option_map (fun NNsuf => traceOf (RollbackConf C C' (head MMsub) (head NNsuf))) NNO) ->
                    (* then reference trace's behavior should prefix that of varied trace *)
                    TracePrefix (ObsTraceOf MMext) (ObsTraceOf NNext) ->
                    ObservableConfidentiality C' MMsub (OptTraceApp MMO MMOrest)) ->
                  ObservableConfidentiality C MM MMOrest.

(* Conjecture we can combine these properties into one by varying for confidentiality and rolling back everything *)
CoInductive ObservableConfidentegrity : Contour -> MTrace -> option MTrace -> Prop :=
| varysafetrace : forall C MM MMOrest,
                    (forall MMsub MMO MMext NN NNO NNext C' N,
                        SubtraceWithSuffix C MM C' MMsub MMO ->
                        variantOf (head MMsub) N C' ->
                        TraceSpan (fun M => ~ (isRet (head MM) M)) (traceOf N) NN NNO ->
                        MMext = TraceApp MMsub MMO ->
                        (* rollback integrity and confidentiality together *)
                        NNext = TraceApp NN (option_map (fun NNsuf => traceOf (Rollback C C' (head MMsub) (head NNsuf))) NNO) ->
                        TracePrefix (ObsTraceOf MMext) (ObsTraceOf NNext) ->
                    ObservableConfidentegrity C' MMsub (OptTraceApp MMO MMOrest)) ->
                  ObservableConfidentegrity C MM MMOrest.

CoInductive LazySafety : MTrace -> Contour -> Prop :=
  ls : forall (MM : MTrace) (C : Contour),
       (ObservableIntegrity C MM None) ->
       (ObservableConfidentiality C MM None) ->
       LazySafety MM C.

CoInductive LazySafety' : MTrace -> Contour -> Prop :=
  ls' : forall (MM : MTrace) (C : Contour),
        ObservableConfidentegrity C MM None ->
        LazySafety' MM C.

(* This confidentiality is more inline with the eager policy, doesn't
   consider later execution *)
Fail
CoInductive LocalConfidentiality : Contour -> MTrace -> Prop :=
  | varytrace : forall C MM,
                  (forall MMsub NN C' M N,
                    Subtrace C MM C' MMsub ->
                    Some M = step (head MMsub) ->
                    variantOf M N C' ->
                    LongestPrefix NN (traceOf N) (fun M => ~ (isRet (head MM) M)) ->
                    TraceEq (ObsTraceOf MM) (ObsTraceOf NN) /\ variantOf (last NN) (last MMsub) C' ->
                    LocalConfidentiality C' MMsub) ->
                  LocalConfidentiality C MM.

Section EagerPolicy.

(* Type of tags and some tags of interest, with a minimalist form of blessed
   call and return sequences. *)
Variable Tag : Type.
Variable Instr : Tag.
Variable Call : Tag.
Variable Ret : Tag.
Variable PCdepth : nat -> Tag.
Variable Stack : nat -> Tag.

(* Machine states are enriched with mappings from components to tags. (Should a
   rich state be a pair of a machine state and the enrichment?) For now, lists
   are used in lieu of sets and an ordering assumed. *)
Definition RichState := Component -> list Tag.
Variable tagsOf : RichState -> Component -> list Tag.

(* Given a call map [cm] and contour [C], relate these to the rich state(s) [T]
   whose tagging is compatible with those. (Add an initial machine state?) *)
Variable InitialTags : CallMap -> Contour -> RichState -> Prop.

Variable updateTag : RichState -> Component -> list Tag -> RichState.

CoInductive TaggedRun : RichState -> MTrace -> Prop :=
| RunFinished : forall T M,
    TaggedRun T (finished M)
| RunCall : forall T T' (M : MachineState) MM d,
    tagsOf T (Reg PC) = [PCdepth d] ->
    tagsOf T (Mem (M (Reg PC))) = [Call; Instr] ->
    updateTag T (Reg PC) [PCdepth (S d)] = T' ->
    TaggedRun T' MM ->
    TaggedRun T (notfinished M MM)
| RunRet : forall T T' (M : MachineState) MM d,
    tagsOf T (Reg PC) = [PCdepth (S d)] ->
    tagsOf T (Mem (M (Reg PC))) = [Instr; Ret] ->
    updateTag T (Reg PC) [PCdepth d] = T' ->
    TaggedRun T' MM ->
    TaggedRun T (notfinished M MM)
(* ... *)
.

(* The eager policy allows a trace if said trace can result from a run of the
   rich machine starting from the initial enriched state. *)
CoInductive EagerPolicyTrace : CallMap -> Contour -> MTrace -> Prop :=
| EPTIntro : forall cm C T MM,
    InitialTags cm C T ->
    TaggedRun T MM ->
    EagerPolicyOK cm MM C.

Conjecture EagerPolicy_StackSafety :
  forall cm MM C,
    EagerPolicyTrace cm C MM ->
    StackSafety cm MM C.

End EagerPolicy.

End foo.

(*
(* Following attempts to encode subtraces that start on transition to NOTME, but can end anywhere as long as still NOTME. 
There is surely still a prettier way! *)


Definition notme (id: Identity) : Prop :=
  match id with
  | NOTME _ _ _ _ => True
  | _ => False
  end.

Definition notme' (cid : Contour * Identity * MachineState) := notme (snd (fst cid)).

CoInductive subtraceAux : CTrace -> MTrace -> Contour -> Prop :=
| subtraceAuxNow: forall C id m MM MM',
     ~ notme id -> TracePrefix MM' MM -> ForallTrace notme' MM' -> subtraceAux (notfinished (C,id,m) MM) (mapTrace snd MM') C
| subtraceAuxLater: forall cim C MM MM' ,  subtraceAux MM MM' C -> subtraceAux (notfinished cim MM) MM' C
.
                                                                      
Definition subtrace (retSP: Value) (cm :CallMap) (C0: Contour) (super: MTrace) (sub: MTrace) (C:Contour) :=
  subtraceAux (CTraceOf retSP C0 super cm) sub C.


(* APT: As things stand, retSP is always initSP.  Is this right? *)
(* LEO: The retSP should always be the stack pointer of the callee of the "initial" process. So when recursing in StackSafety the retSP should be the SP of (head Mcallee) I think. *)
(* APT: Does the adjustment below do the trick? *)

End foo.


(* There are many well-formedness conditions on this... *)
  
Inductive Identity :=
| ME : Value -> (* SP below which I can't access things *) 
       Identity
| NOTME : Value -> (* PC at the time of call *)
          Value -> (* SP at the time of call *)
          nat -> (* local state size *)
          Value -> (* SP of callee *)
          Identity 
| TRANS :
    list Value -> (* Instructions remaining in the sequence *)
    nat ->        (* local state size to be allocated *)
    Value ->      (* PC at the time of call *)
    Value ->      (* SP at the time of call *)
    Value ->      (* SP of callee *)
    Identity.

Definition ITrace := Trace (Identity * MachineState).

(* APT: Recast as operator over MTraces.
        Assumes each call sequence starts with the JAL, right? 
        Is this essential, or was it just to make things a bit simpler? *)
(* LEO: Each call sequence starts with a jal : that makes the
formalization significantly simpler as you can figure out the
information you need for contour changes the moment you start the
transition. Is it too unrealistic an assumption? *)
(* APT: I think this is fine, provided that we allow the callee to
access the piece of the caller’s stack containing the arguments. To do
this, we can add an additional parameter to the call map entries
giving the number of args.  (Note that this prevents our handling
dynamic frame sizes, but that is a feature that is ok to omit at least
at first.)  *) 
(* LEO: Note that this way the handling of arguments/returns is not
part of the blessed sequence. And we could either (1) assume there is
enough local stack space for all calls or (2) handle stack allocation
and deallocation in the contours.  *)

CoFixpoint ITraceOfAux (id : Identity) (MM : MTrace) (M: MachineState) (cm : CallMap) : ITrace :=
  match MM with
  | finished _ => finished (id, M)
  | notfinished _ MM' => 
    let M' := head MM' in
    match id with
    | ME meSP =>
      match find (fun cme =>
                    match cme with
                    | (h::_, _) => valueEq h (valueOf PC M')
                    | _ => false
                    end) cm with
      | Some (seq, sz) =>
        notfinished (id,M) (ITraceOfAux (TRANS seq
                                               sz 
                                               (valueOf PC M')
                                               (valueOf SP M')
                                               meSP)
                                        MM' M' cm)
      | None =>
        notfinished (id,M) (ITraceOfAux (ME meSP) MM' M' cm)
      end
    | TRANS seq sz jalPC jalSP meSP =>
      match seq with
      | _im :: im' :: ims =>
        notfinished (id,M)
                    (ITraceOfAux (TRANS (im' :: ims) sz jalPC jalSP meSP) MM' M' cm)
      | _ =>
        (* Potential check: should be a singleton list always (_im) *)
        notfinished (id, M)
                    (ITraceOfAux (NOTME jalPC jalSP sz meSP) MM' M' cm)
      end
    | NOTME jalPC jalSP sz meSP => 
      if andb (valueEq (valueOf PC M') (vplus jalPC 4))
              (valueEq (valueOf SP M') jalSP) then
        notfinished (id,M) (ITraceOfAux (ME meSP) MM' M' cm)
      else
        notfinished (id,M) (ITraceOfAux (NOTME jalPC jalSP sz meSP) MM' M' cm)
    end
  end.

Definition CTrace := Trace (Contour * Identity * MachineState).

Definition updateContour (C : Contour) (id id' : Identity) (M M' : MachineState) :=
  match id, id' with
  | ME _, ME _ => C
  | NOTME _ _ _ _, NOTME _ _ _ _ => C
  | TRANS _ _ _ _ _, TRANS _ _ _ _ _ => C
  | ME _, TRANS _ sz _ _ _=>
    (* Everything other than the sz top parts of the stack becomes unreachable. *)
    fun k => if cle k (componentOf (vminus (valueOf SP M) sz))
             then (HC, HI) else C k
  | TRANS _ _ _ _ _, NOTME _ jalSP _ _=>
    (* Everything between the size of SP at the call, and the current SP 
       is now "local state" *)
    fun k => if andb (cle k (componentOf (valueOf SP M')))
                     (clt (componentOf jalSP) k)
             then (LC, LI)
             else C k
  | NOTME _ _ (* jalSP *) _ _, ME meSP =>
    (* Everything above the SP at the call becomes unreadable again,
       Everything below the SP but above the low limit of ME becomes
       readable again. *)
    fun k => if andb (clt (componentOf meSP) k)
                     (cle k (componentOf (valueOf SP M')))
             then (LC, LI)
             else if clt (componentOf (valueOf SP M')) k then (HC, HI)
             else C k
  | _, _ => (* ERROR CASE *)
    C 
  end.    

CoFixpoint ContouredTraceOf (C : Contour) (it : ITrace) :=
  match it with
  | finished (id, M) =>
    finished (C, id, M)
  | notfinished (id, M) MM =>
    let (id', M') := head MM in
    let C' := updateContour C id id' M M' in
    notfinished (C, id, M) (ContouredTraceOf C' MM)
  end.

Definition CTraceOf (retSP : Value) (C : Contour) (MM : MTrace) (cm : CallMap) :=
  ContouredTraceOf C (ITraceOfAux (ME retSP) MM (head MM) cm).


Definition updateObs (s : StateObs) (C' : Contour) (M' : MachineState) : StateObs :=
  fun k => match confidentialityOf (C' k) with
           | LC => Some (valueOf k M')
           | HC => s k
           end.

CoFixpoint ObsTraceAux (s : StateObs) (ct : CTrace) : OTrace :=
  match ct with
  | finished (C, id, M) =>
    finished (updateObs s C M)
  | notfinished (C, id, M) CIMs =>
    let s' := updateObs s C M in
    notfinished s' (ObsTraceAux s' CIMs)
  end.
  
Definition ObsTrace (ct : CTrace) : OTrace :=
  let '(C,_,M) := head ct in
  let s0 := fun k =>
              match confidentialityOf (C k) with
              | LC => Some (valueOf k M)
              | HC => None
              end in
  ObsTraceAux s0 ct.


*)
