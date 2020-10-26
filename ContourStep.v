Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

Section WITH_CONTOUR_UPDATE.

  Definition MCPState : Type := MachineState * Contour * PolicyState.
  Definition MCPTrace : Type := TraceOf MCPState.
  
  Variable ContourUpdate : MachineState -> Contour -> Contour.
  
  Definition cstep (mcp:MCPState) : option MCPState :=
    let '(m,c,p) := mcp in
    match mpstep (m,p) with
    | Some ((m',p'),o) =>
      Some (m', ContourUpdate m c, p')
    | None => None
    end.

  Inductive WithContour (c:Contour) : MPTrace -> MCPTrace -> Prop :=
  | WCFinished : forall m p,
      WithContour c (finished (m,p)) (finished (m,c,p))
  | WCNotfinished : forall m p m' c' p' MP MCP,
      WithContour c' MP MCP ->
      cstep (m,c,p) = Some (m',c',p') ->
      head MP = (m',p') -> (* I would like this to check that MP is actually real, is just seems right. *)
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

Definition TraceIntegrity (C:Contour) (M:MTrace) : Prop :=
  forall k m,
    integrityOf (C k) = HI ->
    Last M m ->
    m k = (head M) k.

Inductive ContourSegment (f : Contour -> Prop) : MCPTrace -> MCPTrace -> Prop :=
| CSCurrent : forall MCP MCP' m c p,
    head MCP = (m,c,p) ->
    f c ->
    PrefixUpTo (fun '(m,c,p) => ~ f c) MCP MCP' ->
    ContourSegment f MCP MCP'
| CSLater1 : forall MCP MCPpre MCPsuff MCP' m c p,
    head MCP = (m,c,p) ->
    ~ f c ->
    SplitInclusive (fun '(m,c,p) => f c) MCP MCPpre MCPsuff ->
    ContourSegment f MCPsuff MCP' ->
    ContourSegment f MCP MCP'
| CSLater2 : forall MCP MCPpre MCPsuff MCP' m c p,
    head MCP = (m,c,p) ->
    f c ->
    SplitInclusive (fun '(m,c,p) => ~ f c) MCP MCPpre MCPsuff ->
    ContourSegment f MCPsuff MCP' ->
    ContourSegment f MCP MCP'
.

Definition ContourTraceIntegrity (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' c' p',
    ContourSegment (fun c => integrityOf (c k) = HI) MCP MCP' ->
    head MCP' = (m,c,p) ->
    Last MCP' (m',c',p') ->
    m k = m' k.

Definition variantOf (m n : MachineState) (c : Contour) :=
  forall (k : Component), confidentialityOf (c k) = LC ->
                          m k = n k.

Definition deltaMatch (m m' n n' : MachineState) :=
  forall k,
    (m k <> m' k \/ n k <> n' k) ->
    m' k = n' k.

Definition Stuck (MPO : MPTrace') : Prop :=
  exists m p o,
    Last MPO (m,p,o) ->
    mpstep (m,p) = None.

Definition ContourTraceConfidentiality (MCP:MCPTrace) : Prop :=
  forall k MCP' m c p m' MO MOv,
    ContourSegment (fun c => confidentialityOf (c k) = HC) MCP MCP' ->
    head MCP' = (m,c,p) ->
    variantOf m m' c ->
    ObsOfMCP MCP' MO ->
    MOv = RunOf m' ->
    (forall mend p o,
        Last MO (mend,p,o) ->
        exists m'end o', Last MOv (m'end, o') /\
                         ObsOfMP MO ~=_O ObsOfM MOv /\
                         deltaMatch m mend m' m'end) /\
    (Infinite MO ->
     Infinite MOv /\
     ObsOfMP MO ~=_O ObsOfM MOv) /\
    (Stuck MO ->
     ObsOfMP MO <=_O ObsOfM MOv).

Section WITH_MAPS.

  Variable cdm : CodeMap.
  Variable ym : YieldMap.
  Variable sm : StackMap.
  Variable mpInit : MPState.

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

  Definition CoroutineSafety :=
    forall MCP,
      WithContour coroutineUpdate coroutineInit (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\ ContourTraceConfidentiality MCP.

  (* TODO: create similar for routines *)
  Parameter routineInit : Contour.
  Parameter routineUpdate : MachineState -> Contour -> Contour.

  Definition StackSafety :=
    forall MCP,
      WithContour routineUpdate routineInit (MPTraceOf mpInit) MCP ->
      ContourTraceIntegrity MCP /\ ContourTraceConfidentiality MCP.

End WITH_MAPS.
