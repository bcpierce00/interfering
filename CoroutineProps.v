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

  Variable mpInit : MPState.

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
      MP = MPpre ^ Some MPsuff ->
      ContiguousCorout MPsuff MP' ->
      ContiguousCorout MP MP'
  .

  Inductive ContiguousRout : MPTrace -> MPTrace -> Layout -> Prop :=
  | CRCurrent : forall MP MPpre MPsuff lay,
      SplitInclusive (fun mp => isCall cm (ms mp) lay) MP MPpre MPsuff ->
      ContiguousRout MP MPpre lay
  | CRLater : forall MP MPpre MPsuff MP' lay0 lay,
      ContiguousRout MP MPpre lay0 ->
      MP = MPpre ^ Some MPsuff ->
      ContiguousRout MPsuff MP' lay ->
      ContiguousRout MPsuff MP lay
  .
  
  Inductive AllOfCo : StackID -> MPTrace -> MPTrace -> Prop :=
  | ACCurrent : forall sId MP MPpre MPsuff MPrest,
      SplitInclusive (fun mp => ym ((ms mp) (Reg PC))) MP MPpre MPsuff ->
      (findStack sm ((ms (head MPpre)) (Reg SP))) = Some sId ->
      AllOfCo sId MPsuff MPrest ->
      AllOfCo sId MP (MPpre ^ Some MPrest)
  | ACSkipCurrent : forall sId MP MPpre MPsuff MPrest,
      SplitInclusive (fun mp => ym ((ms mp) (Reg PC))) MP MPpre MPsuff ->
      (findStack sm ((ms (head MPpre)) (Reg SP))) <> Some sId ->
      AllOfCo sId MPsuff MPrest ->
      AllOfCo sId MP MPrest.
  
  Definition TraceIntegrity (C:Contour) (MP:MPTrace) : Prop :=
    forall k mp,
      integrityOf (C k) = HI ->
      Last MP mp ->
      ms mp k = ms (head MP) k.

  Definition CoroutIntegrity : Prop :=
    forall MP C,
      ContiguousCorout (MPTraceOf mpInit) MP ->
      C = makeCoroutContour (ms (head MP)) ->
      TraceIntegrity C MP.

  Definition RoutIntegrity : Prop :=
    forall MP C lay,
      ContiguousRout (MPTraceOf mpInit) MP lay ->
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
    forall MP C,
      ContiguousCorout (MPTraceOf mpInit) MP ->
      C = makeCoroutContour (ms (head MP)) ->
      TraceConfidentiality (fun m => ym (m (Reg PC))) C MP.

  Definition RoutConfidentiality : Prop :=
    forall MP C lay,
      ContiguousRout (MPTraceOf mpInit) MP lay ->
      C = makeRoutContour lay (ms (head MP)) ->
      TraceConfidentiality (fun m => ym (m (Reg PC))) C MP.

  Definition LocalStateEncapsulation : Prop :=
    RoutConfidentiality /\
    RoutIntegrity /\
    CoroutConfidentiality /\
    CoroutIntegrity.

  (* ********************* Control Flow with Coroutines ******************** *)

  Definition ControlSeparation : Prop :=
    forall m1 p1 m2 p2 o n,
      InTrace (m1,p1) (MPTraceOf mpInit) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (m1 (Reg PC)) <> cdm (m2 (Reg PC)) ->
      cm (m1 (Reg PC)) = Some n \/
      rm (m1 (Reg PC)) \/
      ym (m1 (Reg PC)).

  Definition YieldBackIntegrity : Prop :=
    forall mp mp1 mp2 MPout,
      InTrace mp1 (MPTraceOf mp) ->
      ym (ms mp1 (Reg PC)) ->
      SplitInclusive (fun mp2 => sm (ms mp1 (Reg PC)) = sm (ms mp (Reg PC))) (MPTraceOf mp) MPout (MPTraceOf mp2) ->
      justRet (ms mp1) (ms mp2).

  (* UnmatchedReturn cm rm MPO MPO' 
     means that MPO' is the suffix of MPO such that 
     head MPO' is the first unmatched return in MPO *)
  CoInductive UnmatchedReturn : MPTrace -> MPTrace -> Prop :=
  | URNow : forall MP m p,
      head MP = (m,p) ->
      cm (m (Reg PC)) = None ->
      rm (m (Reg PC)) ->
      UnmatchedReturn MP MP
  | URLater : forall MP m p MP',
      cm (m (Reg PC)) = None ->
      ~ rm (m (Reg PC)) ->
      UnmatchedReturn MP MP' ->
      UnmatchedReturn (notfinished (m,p) MP) MP'
  | URCall : forall n MP m p MPcallee mpret MPret MPafter MPresult,
      cm (m (Reg PC)) = Some n ->
      ~ rm (m (Reg PC)) ->
      MP = notfinished (m,p) MPcallee ->
      UnmatchedReturn MPcallee MPret ->
      MPret = (notfinished mpret MPafter) ->
      UnmatchedReturn MPafter MPresult ->
      UnmatchedReturn MP MPresult.

  Definition ReturnIntegrity : Prop :=
    forall sId MP,
      AllOfCo sId (MPTraceOf mpInit) MP ->
      (forall mpcall MPcallee MPret mpret lay,
          ContiguousRout MP (notfinished mpcall MPcallee) lay ->
          UnmatchedReturn MPcallee (notfinished mpret MPret) ->
          justRet (ms mpcall) (ms (head MPret))) /\
      (forall MPret, ~ UnmatchedReturn MP MPret).

  Definition EntryIntegrity : Prop :=
  forall mp1 m2 p2 o n,
    InTrace mp1 (MPTraceOf mpInit) ->
    mpstep mp1 = Some (m2,p2,o) ->
    cm (ms mp1 (Reg PC)) = Some n ->
    em (m2 (Reg PC)).

  Definition WellBracketedControlFlow  : Prop :=
    ControlSeparation /\
    ReturnIntegrity /\
    YieldBackIntegrity /\
    EntryIntegrity.
  
  (* ********************* Coroutine Preservation Across Calls ********************* *)

  Inductive FindYields : MPTrace -> MPState -> MPState -> Prop :=
  | FGNow : forall mp MP,
      ym ((ms mp) (Reg PC)) ->
      FindYields (notfinished mp MP) mp (head MP)
  | FGLater : forall mp MP mp1 mp2,
      FindYields MP mp1 mp2 ->
      FindYields (notfinished mp MP) mp1 mp2.
  
  Definition CoroutinePreservation : Prop :=
    forall mp sId MP mp1 mp2 k,
      AllOfCo sId (MPTraceOf mp) MP ->
      FindYields MP mp1 mp2 ->
      integrityOf ((makeCoroutContour (ms mp1)) k) = HI ->
      ms mp1 k = ms mp2 k.
