Require Import List.
Import ListNotations.
Require Import Bool.

Section foo.

(* TODO: Make all this match the terminology in the .tex -- e.g., a
   Contour should correspond to a MachineState, not to a Trace,
   etc. *)

(* Primitive Abstractions. *)
  
Variable Word : Type.
Variable wlt : Word -> Word -> bool.
Variable weq : Word -> Word -> bool.
Definition wle (w1 w2: Word) : bool := orb (wlt w1 w2) (weq w1 w2).
Variable wplus : Word -> nat -> Word. 
Variable wminus : Word -> nat -> Word. 

Definition Addr : Type := Word.

Variable Register : Type.
Variable PC : Register.
Variable SP : Register.

Inductive Component:=
| Mem (a:Addr)
| Reg (r:Register).

(* A Value is a Word. *)
Definition Value : Type := Word.

(* A Machine State is just a map from Components to Values. *)
Definition MachineState := Component -> Value.

(* Observations are values, or silent (tau) *)
Inductive Observation :=
| Out (w : Word)
| Tau.

(* A Machine State can step to a new Machine State plus an Observation. *)
Variable step : MachineState -> option (MachineState * Observation).

(*******************)
(***** Traces ******)
(*******************)

CoInductive Trace (A : Type) : Type :=
| finished : A -> Trace A
| notfinished : A -> Trace A -> Trace A.

Arguments finished {_} _.
Arguments notfinished {_} _ _.

CoFixpoint mapTrace {A B:Type} (f:A -> B) (MM: Trace A) : Trace B :=
  match MM with
  | finished M => finished (f M)
  | notfinished M MM' => notfinished (f M) (mapTrace f MM')
  end.

CoInductive ForallTrace {A:Type} (P:A -> Prop) : Trace A -> Prop :=
| Forall_finished : forall M, P M -> ForallTrace P (finished M)
| Forall_notfinished : forall M MM', P M -> ForallTrace P MM' -> ForallTrace P (notfinished M MM')
.

Definition MTrace := Trace (MachineState * Observation).

CoFixpoint traceOf (M : MachineState) : MTrace :=
  match step M with
  | None => finished (M,Tau)
  | Some (M',o) => notfinished (M,o) (traceOf M')
  end.

(* LEO: I'm not sure how to satisfy productivity here. We're essentially trying
   to filter a trace. *)
Definition ObsTrace := Trace Observation.

Definition ObsTraceOf (MM: MTrace) : ObsTrace :=
  mapTrace snd MM.

(* OO' either matches OO or deletes some number of Taus *)
CoInductive NoMoreStutter : ObsTrace -> ObsTrace -> Prop :=
| NMSFinTau : forall O,
    NoMoreStutter (notfinished O (finished Tau)) (finished O)
| NMSFinOut : forall w,
    NoMoreStutter (notfinished Tau (finished (Out w))) (finished (Out w))
| NMSMid : forall O OO,
    NoMoreStutter (notfinished Tau (notfinished O OO)) (notfinished O OO)
| NMSLater : forall O OO OO',
    NoMoreStutter OO OO' ->
    NoMoreStutter (notfinished O OO) (notfinished O OO')
| NMSTrans : forall OO OO' OO'',
    NoMoreStutter OO OO' ->
    NoMoreStutter OO' OO'' ->
    NoMoreStutter OO OO''.

Definition Destuttered (OO : ObsTrace) (OO' : ObsTrace) : Prop :=
  NoMoreStutter OO OO' /\ ForallTrace (fun O => O <> Tau) OO'.