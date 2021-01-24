Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.
Require Import TraceProperties.

(* A Domain is an annotation on a component or set of components reflecting its
   relationship to the program state. Domains are nested, so a domain can be subsumed by
   a higher domain, and all of its components with it. For instance, a stack in a coroutine
   system has a domain containing all of the addresses in the stack's range, and the frames
   pushed on the stack each have their own, as described below. *)
Section DOMAIN_MODEL.

  Inductive ShareStatus :=
  | Local
  | Shared
  | Passed
  .
  
  Inductive StackDomain :=
  | Claimed (d:nat)
  | Unclaimed
  .

  Inductive TopDomain :=
  | Instack (sid:StackID) (sd:StackDomain) (ss:ShareStatus)
  | Other
  .

  Definition statusOf td :=
    match td with
    | Instack _ _ ss => Some ss
    | Other => None
    end.

  (* Finally we need a way to map components to the domain they belong to. *)
  Definition DomainMap := Component -> TopDomain.
  Definition DepthMap := StackID -> nat.
  Definition initDepM : DepthMap := fun sid => O.
  Definition push (depm: DepthMap) (sid: StackID) :=
    fun sid' => if stack_eqb sid sid'
                then (depm sid)+1
                else depm sid.
  Definition pop (depm: DepthMap) (sid: StackID) :=
    fun sid' => if stack_eqb sid sid'
                then (depm sid)-1
                else depm sid.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  Variable cdm : CodeMap'.
  Variable sm : StackMap.
  Variable pOf : MachineState -> PolicyState.

  Definition context : Type := DomainMap * DepthMap.
  
  Definition initC : DomainMap * DepthMap :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  match findStack sm a with
                  | Some sid => Instack sid Unclaimed Local
                  | None => Other
                  end
                | Reg r => Other
                end in
    (dm,initDepM).
  
  (* Our update function checks an "annotation" on the code being executed.
     Annotations are defined in Machine.v as an alternative to a million different
     maps, and the ones that matter are call, return, yield, and share.

     Annotations are given by the compiler. We assume that the compiler can tell us
     which instructions represent calls, returns, and yields. Shares are more complicated;
     the compiler cannot directly tell us which component(s) are being shared, because sharing
     is often dynamic. What it can do is identify a relation between the machine state
     and the component(s) being shared.
     
     For an example, suppose that a caller is sharing an address as an argument to its callee.
     It executes a store instruction that the compiler identifies as a share; the target of
     the share is the address to which the argument is being stored, held within the appropriate
     register. So, we would relate a given machine state to the contents of the register in that
     state.
     
     This is a much stronger assumption of information from the compiler than we had before!
     We now fully rely on the compiler to recognize returns, for instance. Relating returns
     to the actual program state is the job of control flow property, WBCF.

     Note that yields don't actually change the domain map, as they don't change which
     addresses belong to which stacks. *)
  
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, depm) := prev in
    match AnnotationOf cdm (m (Reg PC)), findStack sm (m (Reg SP)) with
    | Some (share f), Some sid =>
      let dm' := fun k =>
                   match k with
                   | Mem a =>
                     match f m a, dm k with
                     | Some true, Instack sid' Unclaimed Local =>
                       if stack_eqb sid sid'
                       then Instack sid Unclaimed Passed
                       else dm k
                     | Some false, Instack sid' Unclaimed ss =>
                       if stack_eqb sid sid'
                       then Instack sid Unclaimed Shared
                       else dm k
                     | _, _ => dm k
                     end
                   | _ => dm k
                   end in
      (dm', depm)
    | Some call, Some sid =>
      let dm' := fun k =>
                   match k, dm k with
                   | Mem a, Instack sid' Unclaimed ss =>
                     if andb (wlt a (m (Reg SP))) (stack_eqb sid sid')
                     then Instack sid (Claimed (depm sid)) ss
                     else dm k
                   | _, _ => dm k
                   end in
      (dm', push depm sid)
    | Some ret, Some sid =>
      let dm' := fun k =>
                   match dm k with
                   | Instack sid' (Claimed d) ss =>
                     if andb (stack_eqb sid sid') (d =? (depm sid)-1)
                     then Instack sid Unclaimed Local
                     else dm k
                   | _ => dm k
                   end in
      (dm', pop depm sid)
    | _,_ => (dm,depm)
    end.

  Definition StackInaccessible (c:context) (k:Component) : Prop :=
    exists sid d,
      fst c k = Instack sid (Claimed d) Local \/
      (fst c k = Instack sid (Claimed d) Passed /\ d < (snd c sid)-1).

  Definition CoroutineInaccessible (c:context) (sid:StackID) (k:Component) : Prop :=
    exists sd ss,
      fst c k = Instack sid sd ss /\ ss <> Shared.
  
  Definition StackIntegrityUE : Prop :=
    forall minit k mcp mcp',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished mcp (finished mcp')) ->
      StackInaccessible (cstate mcp) k ->
      mstate mcp k = mstate mcp' k.

  Definition CoroutineIntegrityUE : Prop :=
    forall minit k sid mcp mcp',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished mcp (finished mcp')) ->
      CoroutineInaccessible (cstate mcp) sid k ->
      mstate mcp k = mstate mcp' k.
  
  Definition StackConfidentialityUE : Prop :=
    forall minit m c p m' c' p' p'' n n' o o',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished (m,c,p) (finished (m',c',p'))) ->
      variantOf (fun k => StackInaccessible c k) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p = p'' /\ o = o'.

  Definition CoroutineConfidentialityUE : Prop :=
    forall minit sid m c p m' c' p' p'' n n' o o',
      FindSegmentMP updateC (fun _ _ => False) (minit, pOf minit) initC (notfinished (m,c,p) (finished (m',c',p'))) ->
      variantOf (fun k => CoroutineInaccessible c sid k) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p = p'' /\ o = o'.
  
  Definition StackIntegrityEager : Prop :=
    forall minit MCP d,
      FindSegmentMP updateC (fun m c => snd c = d) (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (StackInaccessible (cstate (head MCP))) MCP.

  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP sid,
      FindSegmentMP updateC (fun m c => activeStack sm m = sid) (minit, pOf minit) initC MCP ->
      TraceIntegrityEager (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) MCP.
  
  Definition Stuck (MCP : @MCPTrace (DomainMap * DepthMap)) : Prop :=
    exists m c p,
      Last MCP (m,c,p) ->
      mpstep (m,p) = None.

  Definition StackConfidentialityEager : Prop :=
    forall minit MCP d sid,
      let P := (fun m c => snd c sid = d) in
      let K := (fun k => StackInaccessible (cstate (head MCP)) k \/
                         exists ss, (fst (cstate (head MCP)) k = Instack sid Unclaimed ss)) in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      TraceConfidentialityEager updateC K P MCP.

  Definition CoroutineConfidentialityEager : Prop :=
    forall minit MCP sid,
      let P := (fun m c => activeStack sm m = sid) in
      let K := (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      TraceConfidentialityEager updateC K P MCP.

  (* ***** Control Flow Properties ***** *)
  
  Definition ControlSeparation : Prop :=
    forall minit m1 p1 m2 p2 o f1 f2 ann1 ann2,
      InTrace (m1,p1) (MPTraceOf (minit, pOf minit)) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (m1 (Reg PC)) = inFun f1 ann1 ->
      cdm (m2 (Reg PC)) = inFun f2 ann2 ->
      f1 <> f2 ->
      AnnotationOf cdm (m1 (Reg PC)) = Some call \/
      AnnotationOf cdm (m1 (Reg PC)) = Some ret \/
      AnnotationOf cdm (m1 (Reg PC)) = Some yield.

  Definition YieldBackIntegrity : Prop :=
    forall mp mp1 mp2 MPout,
      InTrace mp1 (MPTraceOf mp) ->
      AnnotationOf cdm (ms mp1 (Reg PC)) = Some yield ->
      SplitInclusive (fun mp2 => sm (ms mp1 (Reg PC)) = sm (ms mp (Reg PC))) (MPTraceOf mp) MPout (MPTraceOf mp2) ->
      justRet (ms mp1) (ms mp2).

  Definition ReturnIntegrity : Prop :=
    forall sid d minit MCP m c p m' c' p',
      let P := fun m c => activeStack sm m = sid /\ (snd c) sid >= d in
      FindSegmentMP updateC P (minit, pOf minit) initC MCP ->
      head MCP = (m,c,p) ->
      Last MCP (m',c',p') ->
      justRet m m'.

  Variable em:EntryMap.
  
  Definition EntryIntegrity : Prop :=
  forall minit mp1 m2 p2 o,
    InTrace mp1 (MPTraceOf (minit, pOf minit)) ->
    mpstep mp1 = Some (m2,p2,o) ->
    AnnotationOf cdm (ms mp1 (Reg PC)) = Some call ->
    em (m2 (Reg PC)).

  Definition WellBracketedControlFlow  : Prop :=
    ControlSeparation /\
    ReturnIntegrity /\
    YieldBackIntegrity /\
    EntryIntegrity.

End WITH_MAPS.
