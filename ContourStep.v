Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* This file covers a version of the trace properties in which the contour
   is updated at each step.

   Integrity may be defined generically in terms of an initial contour and
   an update function. Confidentiality additionally will need a convergence
   condition. So we will spend some time building up structures for working
   with contours.
   
   First we define the annotation of a trace with contours given some contour
   update function. *)
Section WITH_CONTOUR_UPDATE.

  Definition MCPState : Type := MachineState * Contour * PolicyState.
  Definition MCPTrace : Type := TraceOf MCPState.

  Variable ContourUpdate : MachineState -> Contour -> Contour.

  (* We are using ContourUpdate to define the contour for the next state following a step *)
  Definition cstep (mcp:MCPState) : option MCPState :=
    let '(m,c,p) := mcp in
    match mpstep (m,p) with
    | Some ((m',p'),o) =>
      Some (m', ContourUpdate m c, p')
    | None => None
    end.

  (* WithContour relates an MPtrace to its MCPTrace *)
  Inductive WithContour (c:Contour) : MPTrace -> MCPTrace -> Prop :=
  | WCFinished : forall m p,
      WithContour c (finished (m,p)) (finished (m,c,p))
  | WCNotfinished : forall m p m' c' p' MP MCP,
      WithContour c' MP MCP ->
      cstep (m,c,p) = Some (m',c',p') ->
      head MP = (m',p') -> (* I would like this to check that MP is actually real, it just seems right. *)
      WithContour c (notfinished (m,p) MP) (notfinished (m,c,p) MCP).
  
  (* And similarly, is this a nicer way to handle observations? *)
  Inductive WithObs (o:Observation) : MCPTrace -> MPTrace' -> Prop :=
  | WOFinished : forall m c p,
      WithObs o (finished (m,c,p)) (finished (m,p,o))
  | WONotfinished : forall m c p m' c' o' p' MP MPO,
      WithObs o' MP MPO ->
      mpstep (m,p) = Some ((m',p'),o) ->
      head MP = (m',c',p') ->
      WithObs o (notfinished (m,c,p) MP) (notfinished (m,p,o) MPO).

  Definition ObsOfMCP := WithObs Tau.

End WITH_CONTOUR_UPDATE.

(* ContourSegment takes two conditions, and initial and a final one, and
   relates an MCPTrace to each of its subtraces bracketed by these conditions.
   Each such subtrace must be of length at least two, and an infinite subtrace
   starting with f1 counts. *)
Inductive ContourSegment (f1 f2 : Contour -> Prop) : MCPTrace -> MCPTrace -> Prop :=
| CSCurrent : forall MCP MCP' m c p,
    f1 c ->
    PrefixUpTo (fun '(m,c,p) => f2 c) MCP MCP' ->
    ContourSegment f1 f2 (notfinished (m,c,p) MCP) (notfinished (m,c,p) MCP')
| CSNot : forall MCP MCPpre MCPsuff MCP' m c p,
    head MCP = (m,c,p) ->
    ~ f1 c ->
    SplitInclusive (fun '(m,c,p) => f1 c) MCP MCPpre MCPsuff ->
    ContourSegment f1 f2 MCPsuff MCP' ->
    ContourSegment f1 f2 MCP MCP'
| CSSkip : forall MCP MCPpre MCPsuff MCP' m c p,
    head MCP = (m,c,p) ->
    f1 c ->
    SplitInclusive (fun '(m,c,p) => f2 c) MCP MCPpre MCPsuff ->
    ContourSegment f1 f2 MCPsuff MCP' ->
    ContourSegment f1 f2 MCP MCP'
.

Definition highInt (k:Component) := fun c => integrityOf (c k) = HI.
Definition lowCI (k:Component) := fun c => confidentialityOf (c k) = LC \/ integrityOf (c k) = LI.

(* Integrity on traces is defined as follows: for all k, any state where k is high integrity
   preserves k's value when the trace eventually reaches a state where k is low integrity or
   confidentiality. In other words, from when k becomes off-limits to write to when it might
   be permissibly read or written, it remains the same. *)
Definition ContourTraceIntegrity (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' c' p',
    ContourSegment (highInt k) (lowCI k) MCP MCP' ->
    head MCP' = (m,c,p) ->
    Last MCP' (m',c',p') ->
    m k = m' k.

(* For a lazy variation on integrity, we instead compare the remaining execution to
   one from an idealized state where we roll back improper changes. *)
Definition RollbackInt (C: Contour) (Mstart Mend : MachineState) : MachineState :=
  fun k => match integrityOf (C k) with
           | HI => Mstart k
           | _ => Mend k
           end.

Definition ContourTraceIntegrityLazy (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' c' p',
    ContourSegment (highInt k) (lowCI k) MCP MCP' ->
    head MCP' = (m,c,p) ->
    Last MCP' (m',c',p') ->
    ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf (RollbackInt c m m')).

(* In Confidentiality we will consider variant states, which may differ from the original at
   the appropriate component. We consider only a single component at a time, because we quantify
   over all k when we take the subtrace. *)
Definition variantOf (k : Component) (m n : MachineState) :=
  forall k', k <> k' -> m k = n k.

Definition deltaMatch (m m' n n' : MachineState) :=
  forall k,
    (m k <> m' k \/ n k <> n' k) ->
    m' k = n' k.

Definition Stuck (MPO : MPTrace') : Prop :=
  exists m p o,
    Last MPO (m,p,o) ->
    mpstep (m,p) = None.

(*   |   s1  |  s2   |   s3   |
  k1 [               ]
  k2         [                ] *)

Definition highConf (k:Component) := fun c => confidentialityOf (c k) = HC.
Definition lowConf (k:Component) := fun c => confidentialityOf (c k) = LC.

Definition Converge (m1 m2 : MachineState) :=
  m1 (Reg SP) = m2 (Reg SP) /\ m1 (Reg PC) = m2 (Reg PC).

(*  *)
Definition ContourTraceConfidentiality (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' MO MOv,
    (* for each maximal subtrace on which any k is HC, up to the first time it's LC again *)
    ContourSegment (highConf k) (lowConf k) MCP MCP' ->
    head MCP' = (m,c,p) ->
    ObsOfMCP MCP' MO -> (* we consider the observation-annotated trace *)
    variantOf k m m' -> (* then for any variation on k *)
    (* we consider the observation-annotated trace *)
    RunOf m' = MOv ->
    (* These traces are related in their behavior. They either both converge, both diverge, or the
       original trace gets stuck (fail-stops).*)
    (forall mend c p,
        Last MCP' (mend,c,p) ->
        confidentialityOf (c k) = LC -> (* if we actually get to low confidentiality *)
        exists m'converge o',
          InTrace (m'converge, o') MOv /\ (* then the variant's trace will reach a state that converges *)
          Converge mend m'converge /\
          ObsOfMP MO ~=_O ObsOfM MOv /\ (* both traces have the same observations *)
          deltaMatch m mend m' m'converge) /\ (* the converging states have changed identically *)
    (Infinite MO -> (* if the original trace is infinite, so is the variant, and their traces match *)
     Infinite MOv /\
     ObsOfMP MO ~=_O ObsOfM MOv) /\
    (Stuck MO -> (* and if the original fail-stops, its trace is a prefix of that of the variant *)
     ObsOfMP MO <=_O ObsOfM MOv).

Section WITH_MAPS.

  (* Now that we've described confidentiality and integrity in terms of contours,
     we just need to instantiate the properties by defining how routines and coroutines
     manipulate contours. *)

  Variable cdm : CodeMap.
  Variable cm : CallMap.
  Variable rm : RetMap.
  Variable ym : YieldMap.
  Variable sm : StackMap.
  Variable mpInit : MPState.

  (* For coroutines, initially, the active stack is accessible.
     All other stacks are inaccessible, and registers are accessible.
     Code is readable but not writeable. *)
  Definition coroutineInit :=
    fun k =>
      match k with
      | Mem a =>
        if isCode cdm a
        then (LC,HI)
        else
          if sidEq (findStack sm a) (findStack sm (ms mpInit (Reg SP))) then
            (LC,LI)
          else
            (HC,HI)
      | _ => (LC, LI)
      end.

  (* We update the contour on a yield to make only the new stack accessible. *)
  Definition coroutineUpdate (m : MachineState) (c:Contour) : Contour :=
    if isYield ym (m (Reg PC))
    then
      let m' := step m in
      fun k =>
        match k with
        | Mem a =>
          if sidEq (findStack sm a) (findStack sm (m (Reg SP))) then
            (LC,LI)
          else
            (HC,HI)
        | _ =>
          c k
        end
    else c.

  (* And putting it all together, our final definition of Coroutine Safety *)
  Definition CoroutineSafety :=
    forall MCP,
      WithContour coroutineUpdate coroutineInit (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\
      ContourTraceConfidentiality MCP.

  (* For routines, we start with all stacks uninitialized (HC,LI) *)
  Definition routineInit :=
    fun k =>
      match k with
      | Mem a =>
        if isCode cdm a
        then (LC,HI)
        else (HC,LI)
      | _ => (LC,LI)
      end.

  (* The update is a little more complicated, as it involves a static 
     layout that maps offsets from the stack pointer to booleans: true
     for addresses that should be accessible and false for those that
     should be protected.

     At a call point, everything below the frame pointer remains the
     same; everything above the stack pointer becomes uninitialized,
     and the caller's frame is marked (HC,HI) if the layout considers
     it protected. Otherwise it keeps its old status, which might be
     (HC,LI) if it was never initialized.

     At a return point, we assume that the stack pointer and frame
     pointer have already been restored to their original position.
     Then all that needs to be done is to restore the caller's frame
     to accessibility. Problem: we currently have no way to make sure
     that uninitialized memory that got protected is restored to (HC,LI). *)
  Definition routineUpdate (m:MachineState) (c:Contour) : Contour :=
    fun k =>
      match k with
      | Mem a =>
        match cm a with
        | Some lay =>
          if sidEq (findStack sm a) (findStack sm (m (Reg SP)))
          then if wlt a (m (Reg FP))
               then c k
               else if wlt a (m (Reg SP))
                    then if lay (wminus (m (Reg SP)) (w2nat a))
                         then c k (* Leave alone components that stay accessible, in case they're uninitialized *)
                         else (HC,HI)
                    else (HC,LI)
          else c k
        | None =>
          if isRet rm a
          then if wlt a (m (Reg FP))
               then c k
               else if wlt a (m (Reg SP))
                    then match c k with (* Here is where we set protected components back to accessible *)
                         | (HC,HI) => (LC,LI) (* Problem is they may have been uninitialized before the call *)
                         | _ => c k 
                         end
                    else c k
          else c k
        end
      | _ => (LC,LI)
      end.
  
  Definition StackSafety :=
    forall MCP,
      WithContour routineUpdate routineInit (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\
      ContourTraceConfidentiality MCP.

End WITH_MAPS.
