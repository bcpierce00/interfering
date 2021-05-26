Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.

From StackSafety Require Import Trace MachineModule MapModule PolicyModule CtxModule MPC ObsTrace TraceProperties.

Module SharingDomain (M : Machine) (MM : MapMaker M) <: Ctx M.
  Import M.
  Import MM.

  (* To introduce sharing, we extend our domain model with two new domains:
   Passed indicates memory that is sealed by a function but explicitly designated
   to allow the immediate callee to access it. Shared indicates memory that has been
   explicitly exempted from the sealing convention; once shared, it cannot be sealed
   until the function activation that shared it has returned.

   Unlike sealing, sharing and passing require compiler input to identify instructions
   that share or pass a location. A typical passing instruction is a write to the end
   of the caller's frame, which will be read as a passed argument by the callee. The
   canonical example of sharing is taking the address of a stack variable without
   proving that the address will not escape. There is then no longer a guarantee that
   it will remain protected.

   Some systems make further guarantees, such as using capabilities to ensure that if
   a pointer escapes, the object in question is only accessed in a memory safe way.
   We regard this as a separate property that might well be enforced in parallel to
   stack safety, but is outside of its scope.
 *)
  
  Inductive StackDomain :=
  | Sealed (d:nat)
  | Passed (d:nat)
  | Unsealed
  | Outside
  .

  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Definition sc : SealingConvention :=
    fun m a => wlt a (projw m (Reg SP)).

  (* Likewise, we need to describe what it means to return properly from a call. We parameterize
     this as well, but the standard of course is that the stack pointer must match the original
     call point and the program counter should be one instruction (four cell) later. *)
  Definition ReturnConvention : Type := MachineState -> MachineState -> bool.
  Definition rc : ReturnConvention :=
    fun m1 m2 => weq (projw m1 (Reg SP)) (projw m2 (Reg SP)) &&
                 weq (projw m1 PC) (wplus (projw m2 PC) 4).

  Definition ReturnTargets : Type := list (MachineState -> bool).
  Fixpoint popTo (m:MachineState) (rts : ReturnTargets) : option ReturnTargets :=
    match rts with
    | rt :: rts =>
      if rt m
      then Some rts
      else popTo m rts
    | [] => None
    end.
  
  (* We will use the machinery defined at the end of Machine.v to extend traces of the
     machine with context that will inform our properties. In this case the context is a
     pair of a DomainMap and a ReturnTargets. *)
  
  Definition CtxState : Type := DomainMap * ReturnTargets.

  (* For the initial context, we construct a domain map that maps the stack to Unsealed
     and everything else to Outside. The stack depth is 0. *)
  Definition initCtx (m:MachineState) : CtxState :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Unsealed
                  else Outside
                | _ => Outside
                end in
    (dm, []).
  
  Definition CtxStateUpdate (m:MachineState) (prev:CtxState) : CtxState :=
    let '(dm, rts) := prev in
    match cdm (projw m PC) with
    | Some call =>
      let dm' := fun k =>
                    match k, dm k with
                    | Mem a, Unsealed =>
                      if sc m a
                      then Sealed (length rts)
                      else Unsealed
                    | _, _ => dm k
                    end in
      let rt := rc m in
      (dm', rt::rts)
    | Some (scall f) =>
      let dm' := fun k =>
                   match k, dm k with
                   | Mem a, Unsealed =>
                     if sc m a
                     then if f m a
                          then Passed (length rts)
                          else Sealed (length rts)
                     else Unsealed
                   | _, _ => dm k
                   end in
      let rt := rc m in
      (dm', rt::rts)
    | Some retrn =>
      match popTo (fst (step m)) rts with
      | Some rts' =>
        let d := length rts' in
        let dm' := fun k =>
                     match dm k with
                     | Sealed d' =>
                       if d <=? d' (* Sealed addresses are unsealed when their sealer is returned to/past. *)
                       then Unsealed
                       else dm k
                     | Passed d' =>
                       if d <=? d' (* The same is true of passed addresses; they are single-use *)
                       then Unsealed
                       else dm k
                     | _ => dm k
                     end in
        (dm', rts')
      | None => (dm, rts)
      end
    | _ => (dm, rts)
    end.

  (* A component is inaccessible for writes if it is sealed or if it is passed by the a
     function other than the current one, or its immediate caller. *)
  Definition Inaccessible (c:CtxState) (k:Component) : Prop :=
    exists d,
      fst c k = (Sealed d) \/
      (fst c k = (Passed d) /\ d = (length (snd c))-1).

End SharingDomain.

Module ShareProp (M : Machine) (P : Policy M) (MM : MapMaker M).
  Import M.
  Import P.
  Import MM.
  Module Dom := SharingDomain M MM.
  Export Dom.
  Module MPCImp := MPC M P Dom.
  Import MPCImp.
  Module TPImp := TraceProps M P Dom.
  Import TPImp.

  (* So we can do ultra eager integrity, like before. *)
  Definition StackIntegrityEager : Prop :=
    forall m c p,
      Reachable (m,p,c) ->
      StepIntegrity (Inaccessible c) (m,p,c).
    
  Definition StackConfidentialityEager : Prop :=
    forall MCP d m p c,
      let P := (fun '(m,p,c) => length (snd c) >= d) in
      let K := (fun k => Inaccessible c k \/ (fst c) k = Unsealed) in
      ReachableSegment P MCP ->
      head MCP = (m,p,c) ->
      TraceConfidentialityStep K P MCP.

  (* Continued in Coroutine.v *)
  
End ShareProp.
