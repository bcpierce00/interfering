Require Import List.

Section foo.

(* TODO: Make all this match the terminology in the .tex -- e.g., a
   Contour should correspond to a MachineState, not to a Trace,
   etc. *)

Variable MachineState : Type.
Variable Component : Type.

Variable cle : Component -> Component -> bool.
Variable clt : Component -> Component -> bool.

Variable PC : Component.
Variable SP : Component.

Variable Value : Type.
Variable valueOf : Component -> MachineState -> Value.
Variable valueEq : Value -> Value -> bool.

(* Should this be option? *)
Variable componentOf : Value -> Component.

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

Definition head {A} (MM : Trace A) : A :=
  match MM with
  | finished M => M
  | notfinished M _ => M
  end.

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

Definition variantOf (M N : MachineState) (C : Contour) :=
  forall (k : Component), confidentialityOf (C k) = LC ->
                          valueOf k M = valueOf k N.

(* The values here are the valueOf a sequence of PCs we care about *)
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

CoFixpoint ITraceOfAux (id : Identity) (M : MachineState) (cm : CallMap) :=
  match step M with
  | None => finished (id, M)
  | Some M' =>
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
                                        M' cm)
      | None =>
        notfinished (id,M) (ITraceOfAux (ME meSP) M' cm)
      end
    | TRANS seq sz jalPC jalSP meSP =>
      match seq with
      | _im :: im' :: ims =>
        notfinished (id,M)
                    (ITraceOfAux (TRANS (im' :: ims) sz jalPC jalSP meSP) M' cm)
      | _ =>
        (* Potential check: should be a singleton list always (_im) *)
        notfinished (id, M)
                    (ITraceOfAux (NOTME jalPC jalSP sz meSP) M' cm)
      end
    | NOTME jalPC jalSP sz meSP => 
      if andb (valueEq (valueOf PC M') (vplus jalPC 4))
              (valueEq (valueOf SP M') jalSP) then
        notfinished (id,M) (ITraceOfAux (ME meSP) M' cm)
      else
        notfinished (id,M) (ITraceOfAux (NOTME jalPC jalSP sz meSP) M' cm)
    end
  end.

Definition CTrace := Trace (Contour * Identity * MachineState).

Definition updateContour (C : Contour) (id id' : Identity) (M M' : MachineState) :=
  match id, id' with
  | ME _, ME _ => C
  | NOTME _ _ _ _, NOTME _ _ _ _ => C
  | TRANS _ _ _ _ _, TRANS _ _ _ _ _ => C
  | ME _, TRANS _ sz _ _ _=>
    (* Everything other than the sz top parts of the stuck becomes unreachable. *)
    fun k => if cle k (componentOf (vminus (valueOf SP M) sz))
             then (HC, HI) else C k
  | TRANS _ _ _ _ _, NOTME _ jalSP _ _=>
    (* Everything between the size of SP at the call, and the current SP 
       is now "local state" *)
    fun k => if andb (cle k (componentOf (valueOf SP M')))
                     (clt (componentOf jalSP) k)
             then (LC, LI)
             else C k
  | NOTME _ jalSP _ _, ME meSP =>
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

Definition ComponentObservation := option Value.
Definition StateObservation : Component -> Observation.
  
Variable StackConfidentiality : Trace -> Trace -> Contour -> Prop.
Variable subtrace : Trace -> Trace -> Contour -> Prop.


CoInductive StackSafety : Trace -> Contour -> Prop :=
  ss : forall (MM : Trace) (C : Contour),
       (StackIntegrity MM C) *
       (forall N, variantOf N (fst MM) C ->
                  StackConfidentiality MM (traceOf N) C) *
       (forall Mcallee C',
           subtrace MM Mcallee C' -> StackSafety Mcallee C')
       ->
       StackSafety MM C.

End foo.