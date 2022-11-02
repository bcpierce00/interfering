Require Import String.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import ZArith.
Require Import Nat.

From StackSafety Require Import Trace MachineModule MapModule CtxModule PolicyModule MPC ObsTrace TraceProperties.

Module SimpleDomain (M : Machine) (MM : MapMaker M) <: Ctx M.
  Import M.
  Import MM.

  Inductive StackDomain :=
  | Sealed (d:nat)
  | Unsealed
  | Saved
  | Unsaved
  | Outside
  .

  Definition DomainMap := Component -> StackDomain.  
  
  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Definition sc : SealingConvention :=
    fun m a => wlt a (projw m (Reg SP)).

  Definition SaveConvention : Type := MachineState -> Register -> bool.
  Definition sav : SaveConvention :=
    fun _ r => negb (regEq r SP || regEq r RA).

  Definition ReturnConvention : Type := MachineState -> MachineState -> bool.
  Definition rc : ReturnConvention :=
    fun m1 m2 => weq (projw m1 (Reg SP)) (projw m2 (Reg SP)) &&
                 weq (wplus (projw m1 PC) 4)
                     (wplus (projw m2 PC) 0).

  Definition ReturnTargets : Type := list (MachineState -> bool).
  Fixpoint popTo (m:MachineState) (rts : ReturnTargets) : option ReturnTargets :=
    match rts with
    | rt :: rts =>
      if rt m
      then Some rts
      else popTo m rts
    | [] => None
    end.
    
  Definition CtxState : Type := DomainMap * ReturnTargets.

  Definition initCtx (m:MachineState) : CtxState :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Unsealed
                  else Outside
                | Reg r => Unsaved
                | _ => Outside
                end in
    (dm, []).

  Definition CtxStateUpdate (m:MachineState) (prev:CtxState) : CtxState :=
    let '(dm, rts) := prev in
    match cdm (vtow (proj m PC)) with
    | Some call =>
      let d := length rts in
      let dm' := fun k =>
                    match k, dm k with
                    | Mem a, Unsealed =>
                      if sc m a
                      then Sealed d
                      else Unsealed
                    | Mem a, Sealed d' =>
                      Sealed d'
                    | Reg r, _ =>
                      if sav m r
                      then Saved
                      else Unsaved
                    | _, _ => dm k
                    end in
      let rts' := rc m :: rts in
      (dm', rts')
    | Some ret => 
      match popTo (fst (step m)) rts with
      | Some rts' =>
       (let d := length rts' in
        let dm' := fun k =>
                     match dm k with
                     | Sealed d' =>
                       if d <=? d'
                       then Unsealed
                       else Sealed d'
                     | _ => dm k
                     end in
        (dm', rts'))
      | _ => (dm, rts)
      end
    | _ => (dm, rts)
    end.

  Definition Inaccessible (c : CtxState) (k : Component) : Prop :=
    exists d, (fst c) k = Sealed d \/ (fst c) k = Saved. 

End SimpleDomain.

Module SimpleProp (M : Machine) (P : Policy M) (MM : MapMaker M).
  Import M.
  Import P.
  Import MM.
  Module Dom := SimpleDomain M MM.
  Export Dom.
  Module MPCImp := MPC M P Dom.
  Import MPCImp.
  Module TPImp := TraceProps M P Dom.
  Import TPImp.

  Definition StackIntegrity : Prop :=
    forall MPC d m p c,
      let P := (fun '(m,p,c) => length (snd c) >= d) in
      ReachableSegment P MPC ->
      head MPC = (m,p,c) ->
      TraceIntegrityLazy (Inaccessible c) MPC.
  
  Definition StackConfidentiality : Prop :=
    forall MCP d m p c,
      let P := (fun '(m,p,c) => length (snd c) >= d) in
      let K := (fun k => Inaccessible c k \/ fst c k = Unsealed) in
      ReachableSegment P MCP ->
      head MCP = (m,p,c) ->
      TraceConfidentialityLazy K P MCP.
  
  Definition WellBracketedControlFlow : Prop :=
    forall mpc mpc' o,
      Reachable mpc ->
      mpcstep mpc = Some (mpc',o) ->
      cdm (vtow (proj (mstate mpc) PC)) = Some retrn ->
      exists rt rts,
        snd (cstate mpc) = rt :: rts /\
        snd (cstate mpc') = rts.

End SimpleProp.

