Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.

From StackSafety Require Import Trace MachineModule MapModule PolicyModule CtxModule MPC ObsTrace TraceProperties.


Module CoroutineDomain (M : Machine) (MM : MapMaker M) <: Ctx M.
  Import M.
  Import MM.

  (* We add coroutines with multiple stacks, defined with static extents (see Machine.v).
     Our domain model uses the same stack domain as previous, but now a top-level domain
     combines a stack identity and the domains of that stack. Outside is now a top domain. *)

  Inductive StackDomain :=
  | Sealed (d:nat)
  | Shared (d:nat)
  | Passed (d:nat)
  | Unsealed
  .

  Inductive TopDomain :=
  | Instack (sid:StackID) (sd:StackDomain)
  | Outside
  .

  Definition DomainMap := Component -> TopDomain.
  
  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Definition sc : SealingConvention :=
    fun m a =>
      match wtoa (projw m (Reg SP)) with
      | Some a' => alt a a'
      | None => false
      end.

  (* Likewise, we need to describe what it means to return properly from a call. We parameterize
     this as well, but the standard of course is that the stack pointer must match the original
     call point and the program counter should be one instruction (four cell) later. *)
  Definition ReturnConvention : Type := MachineState -> MachineState -> bool.
  Definition rc : ReturnConvention :=
    fun m1 m2 => weq (projw m1 (Reg SP)) (projw m2 (Reg SP)) &&
                 weq (projw m1 PC) (wplus (projw m2 PC) 4).

  Definition Target : Type := MachineState -> bool.
  
  Definition ReturnTargets : Type := list Target.
  Fixpoint popTo (m:MachineState) (rts : ReturnTargets) : option ReturnTargets :=
    match rts with
    | rt :: rts =>
      if rt m
      then Some rts
      else popTo m rts
    | [] => None
    end.

  Definition RTSMap : Type := StackID -> ReturnTargets.
  Definition initRM : RTSMap := fun sid => [].
  Definition push (rm : RTSMap) (sid: StackID) (rt : Target) :=
    fun sid' => if stack_eqb sid sid'
                then rt::(rm sid)
                else rm sid.
  Definition pop (rm: RTSMap) (sid: StackID) (m: MachineState) :=
    fun sid' => if stack_eqb sid sid'
                then match popTo m (rm sid') with
                     | Some rts => rts
                     | None => rm sid'
                     end
                else rm sid.

  Definition YieldTargets := StackID -> option Target.
  Definition updateYT (yt:YieldTargets) (sid:StackID) (t:Target) :=
    fun sid' => if stack_eqb sid sid' then Some t else yt sid'.

  (* We will use the machinery defined at the end of Machine.v to extend traces of the
     machine with context that will inform our properties. In this case the context is a
     pair of a DomainMap and a ReturnTargets. *)
  Definition CtxState : Type := DomainMap * RTSMap * YieldTargets * StackID.

  Definition dmof (c:CtxState) :=
    let '(dm,_,_,_) := c in dm.
  Definition rmof (c:CtxState) :=
    let '(_,rm,_,_) := c in rm.
  Definition ytof (c:CtxState) :=
    let '(_,_,yt,_) := c in yt.
  Definition sidof (c:CtxState) :=
    let '(_,_,_,sid) := c in sid.
  
  Definition initCtx (m:MachineState) : CtxState :=
    let sid := match activeStack sm m with
               | Some sid => sid
               | None => defaultStack
               end in
    let dm := fun k =>
                match k with
                | Mem a =>
                  match sm a with
                  | Some sid => Instack sid Unsealed
                  | None => Outside
                  end
                | Reg r => Outside
                | PC => Outside
                end in
    (dm,initRM,fun _ => None,sid).
  
  Definition flatten {A} (o:option (option A)) : option A :=
    match o with
    | Some (Some o') => Some o'
    | _ => None
    end.

  Definition CtxStateUpdate (m:MachineState) (prev:CtxState) : CtxState :=
    let '(dm,rm,yt,sid) := prev in
    match flatten (option_map cdm (wtoa (projw m PC))) with
    | Some call =>
      let dm' := fun k =>
                   match k, dm k with                      
                   | Mem a, Instack sid' Unsealed =>
                     if sc m a && stack_eqb sid sid'
                     then Instack sid (Sealed (length (rm sid)))
                     else Instack sid Unsealed
                   | _, _ => dm k
                   end in
      let rm' := push rm sid (rc m) in
      (dm', rm', yt, sid)
    | Some (scall f) =>
      let dm' := fun k =>
                   match k, dm k with
                   | Mem a, Instack sid' Unsealed =>
                     if sc m a && stack_eqb sid sid'
                     then if f m a
                          then Instack sid (Passed (length (rm sid)))
                          else Instack sid (Sealed (length (rm sid)))
                     else Instack sid Unsealed
                   | _, _ => dm k
                   end in
      let rm' := push rm sid (rc m) in
      (dm', rm', yt, sid)
    | Some retrn =>
      let rm' := pop rm sid m in
      let d := length (rm sid) in
      let dm' := fun k =>
                   match dm k with
                   | Instack sid' (Sealed d') =>
                     if (d <=? d') && stack_eqb sid sid'
                     then Instack sid Unsealed
                     else dm k
                   | Instack sid' (Passed d') =>
                     if (d <=? d') && stack_eqb sid sid'
                     then Instack sid Unsealed
                     else dm k
                   | _ => dm k
                   end in
      (dm', rm', yt, sid)
    | Some yield =>
      let m' := fst (step m) in
      match activeStack sm m with
      | Some sid' =>
        match yt sid' with
        | Some t =>
          if t m'
          then (dm,rm,updateYT yt sid (rc m),sid')
          else prev
        | None => (dm,rm,updateYT yt sid (rc m),sid')
        end
      | _ => prev
      end
    | _ => prev
    end.

  Definition StackInaccessible (c:CtxState) (k:Component) : Prop :=
    exists sid d,
      dmof c k = Instack sid (Sealed d) \/
      (dmof c k = Instack sid (Passed d) /\ d = (length (rmof c sid))+1).

  (* We split up our inaccessibility criterion into stack and coroutine variations.
     The coroutine version takes the active stack, and prohibits accessing other stacks
     except for shared objects. *)
  Definition CoroutineInaccessible (c:CtxState) (sid:StackID) (k:Component) : Prop :=
    forall sid' sd d,
      dmof c k = Instack sid' sd ->
      (sid <> sid /\ sd <> Shared d).

End CoroutineDomain.

Module CoroutProp (M : Machine) (P : Policy M) (MM : MapMaker M).
  Import M.
  Import P.
  Import MM.
  Module Dom := CoroutineDomain M MM.
  Export Dom.
  Module MPCImp := MPC M P Dom.
  Import MPCImp.
  Module TPImp := TraceProps M P Dom.
  Import TPImp.
  
  Definition StackIntegrityEager : Prop :=
    forall k m c p m' p' c' o,
      Reachable (m,p,c) ->
      mpcstep (m,p,c) = Some (m',p',c',o) ->
      StackInaccessible c k ->
      proj m k = proj m' k.
  
  Definition CoroutineIntegrityEager : Prop :=
    forall m c p,
      Reachable (m,p,c) ->
      StepIntegrity (fun k => sm (projw m k) = activeStack sm m) (m,p,c).

  Definition StackConfidentialityEager : Prop :=
    forall sid MCP d m dm depm p,
      let P := (fun '(m,p,c) => length (rmof c sid) >= d) in
      let K := (fun k => StackInaccessible (cstate (head MCP)) k \/
                         dmof (cstate (head MCP)) k = Instack sid Unsealed) in
      ReachableSegment P MCP ->
      head MCP = (m,p,(dm,depm)) ->
      TraceConfidentialityStep K P MCP.
  
  Definition CoroutineConfidentialityEager : Prop :=
    forall MPC sid,
      let P := (fun '(m,p,c) => activeStack sm m = Some sid) in
      let K := (fun k => flatten (option_map sm (wtoa (projw (mstate (head MPC)) k))) =
                         activeStack sm (mstate (head MPC))) in
      ReachableSegment P MPC ->
      TraceConfidentialityStep K P MPC.

  (* Observational *)

  Definition StackIntegriityObservational : Prop :=
    forall sid MCP d m dm depm p,
      let P := (fun '(m,p,c) => length (rmof c sid) >= d) in
      let K := (fun k => StackInaccessible (cstate (head MCP)) k) in
      ReachableSegment P MCP ->
      head MCP = (m,p,(dm,depm)) ->
      TraceIntegrityObs K MCP.
  
  Definition CoroutineIntegrityObervational : Prop :=
    forall sid MCP m dm depm p,
      let P := (fun '(m,p,c) => activeStack sm m = Some sid) in
      let K := (fun k => sm (projw (mstate (head MCP)) k) = activeStack sm (mstate (head MCP))) in
      ReachableSegment P MCP ->
      head MCP = (m,p,(dm,depm)) ->
      TraceIntegrityObs K MCP.
    
  Definition StackConfidentialityObservational : Prop :=
    forall sid MCP d m dm depm p,
      let P := (fun '(m,p,c) => length (rmof c sid) >= d) in
      let K := (fun k => StackInaccessible (cstate (head MCP)) k \/
                         dmof (cstate (head MCP)) k = Instack sid Unsealed) in
      ReachableSegment P MCP ->
      head MCP = (m,p,(dm,depm)) ->
      TraceConfidentialityObs K P MCP.
  
  Definition CoroutineConfidentialityObservational : Prop :=
    forall MPC sid,
      let P := (fun '(m,p,c) => activeStack sm m = Some sid) in
      let K := (fun k => sm (projw (mstate (head MPC)) k) = activeStack sm (mstate (head MPC))) in
      ReachableSegment P MPC ->
      TraceConfidentialityObs K P MPC.

  
  (* ***** Control Flow Properties ***** *)

  (* Finally, we also need to consider control flow properties. *)

  Definition YieldBackIntegrity : Prop :=
    forall mpc1 mpc2,
      let P := (fun mpc => flatten (option_map sm (wtoa (projw (mstate mpc1) (Reg SP))))
                           = flatten (option_map sm (wtoa (projw (mstate mpc) (Reg SP))))) in
      Reachable mpc1 ->
      flatten (option_map cdm (wtoa (projw (mstate mpc1) PC))) = Some yield ->
      StepsToWhen P mpc1 mpc2 ->
      justRet (mstate mpc1) (mstate mpc2).

  Definition ReturnIntegrity : Prop :=
    forall d sid MCP m c p m' c' p',
      let P := fun '(m,p,c) => activeStack sm m = Some sid /\ length (rmof c sid) >= d in
      ReachableSegment P MCP ->
      head MCP = (m,c,p) ->
      Last MCP (m',c',p') ->
      justRet m m'.
 
  Definition WellStructuredControlFlow  : Prop :=
    ReturnIntegrity /\
    YieldBackIntegrity.

End CoroutProp.
