Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

Section WITH_MAPS.
  Variable cdm : CodeMap.
  Variable cm : CallMap.
  Variable rm : RetMap.
  Variable sm : StackMap.
  Variable ym : YieldMap.
  Variable em : EntryMap.

  Definition accessible (addr sp : Addr) (lay : Layout) : bool :=
    lay (wminus sp (w2nat addr)).

  Definition makeCoroutContour (m : MachineState) : Contour :=
    fun k =>
      match k with
      | Mem a =>
        if isCode cdm a then
          (LC,HI)
        else
          if sidEq (findStack sm a) (findStack sm (m (Reg SP))) then
            (LC,LI)
          else
            (HC,HI)
      | _ => (LC, LI)
      end.

  Definition makeRoutContour (lay : Layout) (m : MachineState) : Contour :=
    fun k =>
      match k with
      | Mem a =>
        if isCode cdm a then
          (LC,HI)
        else
          if sidEq (findStack sm a) (findStack sm (m (Reg SP))) then
            if wlt (m (Reg SP)) a then
              (HC, LI)
            else if accessible a (m (Reg SP)) lay then
                   (LC, LI)
                 else
                   (HC, HI)
          else
            (LC,LI)
      | _ => (LC, LI)
      end.

  Inductive ContiguousCorout : MPTrace -> MPTrace -> Prop :=
  | CCCurrent : forall MP MPpre MPsuff,
      SplitInclusive (fun mp => ym ((ms mp) (Reg PC))) MP MPpre MPsuff ->
      ContiguousCorout MP MPpre
  | CCLater : forall MP MPpre MPsuff MP',
      ContiguousCorout MP MPpre ->
      JoinInclusive MPpre MPsuff = MP ->
      ContiguousCorout MPsuff MP' ->
      ContiguousCorout MP MP'
  .

  Inductive ContiguousRout : MPTrace -> MPTrace -> Layout -> Prop :=
  | CRCurrent : forall MP MPpre MPsuff lay,
      SplitInclusive (fun mp => isCall cm (ms mp) lay) MP MPpre MPsuff ->
      ContiguousRout MP MPpre lay
  | CRLater : forall MP MPpre MPsuff MP' lay0 lay,
      ContiguousRout MP MPpre lay0 ->
      JoinInclusive MPpre MPsuff = MP ->
      ContiguousRout MPsuff MP' lay ->
      ContiguousRout MPsuff MP lay
  .

  Definition TraceIntegrity (C:Contour) (MP:MPTrace) : Prop :=
    forall k mp,
      integrityOf (C k) = HI ->
      Last MP mp ->
      ms mp k = ms (head MP) k.

  Definition CoroutineIntegrity : Prop :=
    forall mp MP C,
      ContiguousCorout (MPTraceOf mp) MP ->
      C = makeCoroutContour (ms (head MP)) ->
      TraceIntegrity C MP.

  Definition RoutineIntegrity : Prop :=
    forall mp MP C lay,
      ContiguousRout (MPTraceOf mp) MP lay ->
      C = makeRoutContour lay (ms (head MP)) ->
      TraceIntegrity C MP.

  Definition variantOf (m n : MachineState) (C : Contour) :=
    forall (k : Component), confidentialityOf (C k) = LC ->
                            m k = n k.

  Definition deltaMatch (m m' n n' : MachineState) :=
    forall k,
      (m k <> m' k \/ n k <> n' k) ->
      m' k = n' k.

  Definition TraceConfidentiality (endCond : MachineState -> Prop) (C:Contour) (MP:MPTrace) : Prop :=
    forall mp m' mpend M',
      variantOf (ms mp) m' C ->
      PrefixUpTo endCond (MTraceOf m') M' ->
      (Last MP mpend ->
       endCond (ms mpend) ->
       exists m'end,
         Last M' m'end /\
         ObsTraceOf MP ~=_O ObsTraceOfM M' /\
         deltaMatch (ms mp) (ms mpend) m' m'end) /\
      (Last MP mpend ->
       ~ endCond (ms mpend) ->
       ObsTraceOf MP <=_O ObsTraceOfM M') /\
      (Infinite MP ->
       Infinite M' /\
       ObsTraceOf MP <=_O ObsTraceOfM M').

  Definition CoroutConfidentiality : Prop :=
    forall mp MP C,
      ContiguousCorout (MPTraceOf mp) MP ->
      C = makeCoroutContour (ms (head MP)) ->
      TraceConfidentiality (fun m => ym (m (Reg PC))) C MP.

  Definition RoutConfidentiality : Prop :=
    forall mp MP C lay,
      ContiguousRout (MPTraceOf mp) MP lay ->
      C = makeRoutContour lay (ms (head MP)) ->
      TraceConfidentiality (fun m => ym (m (Reg PC))) C MP.

  (* ********************* Control Flow with Coroutines ******************** *)

  Definition ControlSeparation : Prop :=
    forall mp m1 p1 m2 p2 o n,
      InTrace (m1,p1) (MPTraceOf mp) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (m1 (Reg PC)) <> cdm (m2 (Reg PC)) ->
      cm (m1 (Reg PC)) = Some n \/
      rm (m1 (Reg PC)) \/
      ym (m1 (Reg PC)).

  Definition YieldBackIntegrity : Prop :=
    forall mp mp1 mp2 m3 p3 o MPout,
      InTrace mp1 (MPTraceOf mp) ->
      ym (ms mp1 (Reg PC)) ->
      SplitInclusive (fun mp2 => sm (ms mp1 (Reg PC)) = sm (ms mp (Reg PC))) (MPTraceOf mp) MPout (MPTraceOf mp2) ->
      mpstep mp1 = Some (m3,p3,o) ->
      m3 (Reg SP) = ms mp1 (Reg SP) /\
      m3 (Reg PC) = wplus (ms mp1 (Reg PC)) 4.
