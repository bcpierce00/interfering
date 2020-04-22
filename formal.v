Require Import List.

Section foo.

(* TODO: Make all this match the terminology in the .tex -- e.g., a
   Contour should correspond to a MachineState, not to a Trace,
   etc. *)

Variable MachineState : Type.
Variable Component : Type.

(* APT: Since Components include registers, these aren't total orders, which is confusing. 
        Maybe we should get more honest about the makeup of Components?
        Or : just do these comparisons on Values; then we don't really need componentOf. *)
Variable cle : Component -> Component -> bool.
Variable clt : Component -> Component -> bool.

Variable PC : Component.
Variable SP : Component.

Variable Value : Type.
Variable valueOf : Component -> MachineState -> Value.
Variable valueEq : Value -> Value -> bool.

(* Should this be option? *)
(* APT: See above. *)
Variable componentOf : Value -> Component.

Variable initSP : Value.
Variable JAL : Value.
Variable incr : Value -> Value.
Variable vplus : Value -> nat -> Value.
Variable vminus : Value -> nat -> Value.
Variable veq : Value -> Value -> bool.
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
                            valueOf k M0 = valueOf k (head MM)) ->
    StackIntegrity C MM ->
    StackIntegrity C (notfinished M0 MM).


(* APT: An equivalent alternative definition that more closely matches the latex... *)

Definition StackIntegrity' (C : Contour) (MM: MTrace) : Prop :=
    forall (k: Component), integrityOf (C k) = HI ->
      forall (m: MachineState), InTrace m MM -> valueOf k (head MM) = valueOf k m.

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
                          valueOf k M = valueOf k N.

(* The values here are the valueOf a sequence of PCs we care about *)
(* APT: ? the addresses or the instructions in them? Doesn't seem to be used in either case; why not just track its length? *)
Definition CallMap := list (list Value * nat)%type.
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

(* CoFixpoint ITraceOfAux (id : Identity) (M : MachineState) (cm : CallMap) : ITrace := *)
(*   match step M with *)
(*   | None => finished (id, M) *)
(*   | Some M' => *)
(*     match id with *)
(*     | ME meSP => *)
(*       match find (fun cme => *)
(*                     match cme with *)
(*                     | (h::_, _) => valueEq h (valueOf PC M') *)
(*                     | _ => false *)
(*                     end) cm with *)
(*       | Some (seq, sz) => *)
(*         notfinished (id,M) (ITraceOfAux (TRANS seq *)
(*                                                sz  *)
(*                                                (valueOf PC M') *)
(*                                                (valueOf SP M') *)
(*                                                meSP) *)
(*                                         M' cm) *)
(*       | None => *)
(*         notfinished (id,M) (ITraceOfAux (ME meSP) M' cm) *)
(*       end *)
(*     | TRANS seq sz jalPC jalSP meSP => *)
(*       match seq with *)
(*       | _im :: im' :: ims => *)
(*         notfinished (id,M) *)
(*                     (ITraceOfAux (TRANS (im' :: ims) sz jalPC jalSP meSP) M' cm) *)
(*       | _ => *)
(*         (* Potential check: should be a singleton list always (_im) *) *)
(*         notfinished (id, M) *)
(*                     (ITraceOfAux (NOTME jalPC jalSP sz meSP) M' cm) *)
(*       end *)
(*     | NOTME jalPC jalSP sz meSP =>  *)
(*       if andb (valueEq (valueOf PC M') (vplus jalPC 4)) *)
(*               (valueEq (valueOf SP M') jalSP) then *)
(*         notfinished (id,M) (ITraceOfAux (ME meSP) M' cm) *)
(*       else *)
(*         notfinished (id,M) (ITraceOfAux (NOTME jalPC jalSP sz meSP) M' cm) *)
(*     end *)
(*   end. *)


(* APT: Recast as operator over MTraces.
        Assumes each call sequence starts with the JAL, right? 
        Is this essential, or was it just to make things a bit simpler? *)
CoFixpoint ITraceOfAux' (id : Identity) (MM : MTrace) (M: MachineState) (cm : CallMap) : ITrace :=
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
        notfinished (id,M) (ITraceOfAux' (TRANS seq
                                               sz 
                                               (valueOf PC M')
                                               (valueOf SP M')
                                               meSP)
                                        MM' M' cm)
      | None =>
        notfinished (id,M) (ITraceOfAux' (ME meSP) MM' M' cm)
      end
    | TRANS seq sz jalPC jalSP meSP =>
      match seq with
      | _im :: im' :: ims =>
        notfinished (id,M)
                    (ITraceOfAux' (TRANS (im' :: ims) sz jalPC jalSP meSP) MM' M' cm)
      | _ =>
        (* Potential check: should be a singleton list always (_im) *)
        notfinished (id, M)
                    (ITraceOfAux' (NOTME jalPC jalSP sz meSP) MM' M' cm)
      end
    | NOTME jalPC jalSP sz meSP => 
      if andb (valueEq (valueOf PC M') (vplus jalPC 4))
              (valueEq (valueOf SP M') jalSP) then
        notfinished (id,M) (ITraceOfAux' (ME meSP) MM' M' cm)
      else
        notfinished (id,M) (ITraceOfAux' (NOTME jalPC jalSP sz meSP) MM' M' cm)
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

(* Definition CTraceOf (retSP : Value) (C : Contour) (M : MachineState) (cm : CallMap) := *)
(*   ContouredTraceOf C (ITraceOfAux (ME retSP) M cm). *)

(* APT: Recast as operator over MTraces *)
Definition CTraceOf' (retSP : Value) (C : Contour) (MM : MTrace) (cm : CallMap) :=
  ContouredTraceOf C (ITraceOfAux' (ME retSP) MM (head MM) cm).

Definition CompObs := option Value.
Definition StateObs := Component -> CompObs.

Definition OTrace := Trace StateObs.

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

CoInductive TracePrefix {A} : Trace A -> Trace A -> Prop :=
| PrefixEq  : forall m, TracePrefix (finished m) (finished m)
| PrefixNow : forall m mm, TracePrefix (finished m) (notfinished m mm)
| PrefixLater : forall m mm1 mm2, TracePrefix mm1 mm2 ->
                                  TracePrefix (notfinished m mm1)
                                              (notfinished m mm2).

(* Definition StackConfidentiality (retSP : Value) (cm : CallMap) *)
(*            (C : Contour) (M : MachineState) := *)
(*   forall N, variantOf M N C -> *)
(*             let o  := ObsTrace (CTraceOf retSP C M cm) in *)
(*             let o' := ObsTrace (CTraceOf retSP C N cm) in *)
(*             TracePrefix o o' \/ TracePrefix o' o. *)

(* APT: Surely this needs to be defined on a trace with a potential
stopping point, not just on a starting state?  
*)
Definition StackConfidentiality (retSP : Value) (cm : CallMap)
           (C : Contour) (MM : MTrace) := 
  forall N, variantOf (head MM) N C ->
            let o  := ObsTrace (CTraceOf' retSP C MM cm) in
            let o' := ObsTrace (CTraceOf' retSP C (traceOf N) cm) in
            TracePrefix o o'.  (* just this direction: it would be bad if variant trace ended sooner than reference, right? *)


(* Following attempts to encode subtraces that start on transition to NOTME, but can end anywhere as long as still NOTME. 
There is surely a prettier way! *)

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
  subtraceAux (CTraceOf' retSP C0 super cm) sub C.


(* APT: As things stand, retSP is always initSP.  Is this right? *)
CoInductive StackSafety (cm : CallMap) : MTrace -> Contour -> Prop :=
  ss : forall (MM : MTrace) (C : Contour),
       (StackIntegrity C MM) ->
       (StackConfidentiality initSP cm C MM (* (head MM)*)) ->
       (forall Mcallee C', subtrace initSP cm C MM Mcallee C' -> StackSafety cm Mcallee C') ->
       StackSafety cm MM C.

End foo.