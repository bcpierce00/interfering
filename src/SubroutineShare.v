Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.

From StackSafety Require Import Trace MachineImpl ObsTrace TraceProperties.

(*
Module SubroutineShare (M: MachineSpec).
  Import M.
  Module O := ObsTrace(M).
  Import O.
  Module TP := TraceProperties(M).
  Import TP.
*)
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
Section DOMAIN_MODEL.
  
  Inductive StackDomain :=
  | Sealed (d:nat)
  | Shared (d:nat)
  | Passed (d:nat)
  | Unsealed
  | Outside
  .

  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  Variable cdm : CodeMap. (* Map of where code lives in memory and its annotation. *)
  Variable sm : Addr -> bool. (* Determines whether an address is in the stack. *)
  Variable pOf : MachineState -> PolicyState. (* Policy initialization function. *)

  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Variable sc : SealingConvention.
  
  Definition context : Type := DomainMap * nat.

  (* For the initial context, we construct a domain map that maps the stack to Unsealed
     and everything else to Outside. The stack depth is 0. *)
  Definition initC : context :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Unsealed
                  else Outside
                | _ => Outside
                end in
    (dm, O).
  
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, d) := prev in
    match AnnotationOf cdm (proj m PC) with
    | Some (share f) =>
      let dm' := fun k =>
                   match k with
                   | Mem a =>
                     match f m a, dm k with
                     | Some true, Unsealed => Passed d
                     | Some false, Unsealed => Shared d
                     | _, _ => dm k
                     end
                   | _ => dm k
                   end in
      (dm', d)
    | Some call =>
      let dm' := fun k =>
                    match k, dm k with                      
                    | _, Sealed d => Sealed d (* Fix alll this *)
                    | _, Outside => Outside
                    | Mem a, _ =>
                      if sc m a
                      then Sealed d
                      else Unsealed (* If addresses are marked to be shared but the sealing convention
                                       wants them unsealed, the sealing convention takes precedence *)
                    | _, _ => dm k
                    end in
      (dm', d+1)
    | Some ret => 
      let dm' := fun k =>
                    match dm k with
                    | Sealed d' =>
                      if (d-1) =? d' (* Sealed addresses are unsealed when their sealer is returned to. *)
                      then Unsealed
                      else dm k
                    | Passed d' =>
                      if (d-1) =? d' (* The same is true of passed addresses; they are single-use *)
                      then Unsealed
                      else dm k
                    | Shared d' =>
                      if d =? d' (* But shared addresses persist until the sharer itself returns *)
                      then Unsealed
                      else dm k
                    | _ => dm k
                    end in
      (dm', d-1)
    | _ => (dm, d)
    end.

  (* A component is inaccessible for writes if it is sealed or if it is passed by the a
     function other than the current one, or its immediate caller. *)
  Definition Inaccessible (c:context) (k:Component) : Prop :=
    exists d,
      fst c k = (Sealed d) \/
      (fst c k = (Passed d) /\ d < (snd c)-1).

  (* So we can do ultra eager integrity, like before. *)
  Definition StackIntegrityEager : Prop :=
    forall m c p,
      Reachable updateC initC (m,p,c) ->
      StepIntegrity updateC (Inaccessible c) (m,p,c).
    
  Definition StackConfidentialityEager : Prop :=
    forall MCP d m dm p,
      let P := (fun '(m,p,c) => snd c >= d) in
      let K := (fun k => Inaccessible (dm,d) k \/ dm k = Unsealed) in
      ReachableSegment updateC initC P MCP ->
      head MCP = (m,p,(dm,d)) ->
      TraceConfidentialityStep updateC K P MCP.

  (* Continued in Coroutine.v *)
  
End WITH_MAPS.

(*
End SubroutineShare.
*)
