From StackSafety Require Import MachineModule TestingModules DefaultLayout RISCVMachine RISCVObs.

Require Import String.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import ZArith.
Require Import Nat.

Module TestSimpleDomain (M : Machine) (LI : LayoutInfo M) <: TestCtx M LI.
  Import M.
  Import LI.
  
  Inductive StackDomain :=
  | Sealed (d:nat)
  | Unsealed
  | Outside
  .

  Definition SD_eqb s1 s2 :=
    match s1, s2 with
    | Sealed n1, Sealed n2 => Nat.eqb n1 n2
    | Unsealed, Unsealed   => true
    | Outside,  Outside    => true
    | _, _ => false
    end.

  Definition DomainMap := Element -> StackDomain.
  
  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Definition sc : SealingConvention :=
    fun m a =>
      let a' := proj m (Reg SP) in
      wlt a a'.

  (* Likewise, we need to describe what it means to return properly from a call. We parameterize
     this as well, but the standard of course is that the stack pointer must match the original
     call point and the program counter should be one instruction (four cell) later. *)
  Definition ReturnConvention : Type := MachineState -> MachineState -> bool.
  Definition rc : ReturnConvention :=
    fun m1 m2 => weq (proj m1 (Reg SP)) (proj m2 (Reg SP)) &&
                 weq (wplus (proj m1 PC) 4)
                     (wplus (proj m2 PC) 0).

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

  Definition interestingComponent (c c' : CtxState) (k : Element) :=
    negb (SD_eqb (fst c k) (fst c' k)).

  Definition integrityComponent (c : CtxState) (k : Element) :=
    match fst c k with
    | Sealed _ => true
    | _ => false
    end.

  Definition confidentialityComponent (c : CtxState) (k : Element) :=
    match fst c k with
    | Sealed _ => true
    | Unsealed => true
    | _ => false
    end.

  Definition depthOf (c : CtxState) := length (snd c).
  
  Definition initCtx (li:LayoutInfo) : CtxState :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if defStackMap li a
                  then Unsealed
                  else Outside
                | _ => Outside
                end in
    (dm, []).

  Definition flatten {A} (o:option (option A)) : option A :=
    match o with
    | Some (Some o') => Some o'
    | _ => None
    end.

  (* Quick and dirty, extract the relevant information from a set of operations
     (i.e., a subset of the old type of code annotations) *)
  Inductive CallRet : Set :=
  | CRcall
  | CRret
  | CRnone.

  Definition CallRet_eqb (cr1 cr2 : CallRet) : bool :=
    match cr1, cr2 with
    | CRcall, CRcall | CRret, CRret | CRnone, CRnone => true
    | _, _ => false
    end.

  Definition op_callret (o : Operation) : CallRet :=
    match o with
    | Call _ _ _
    | Tailcall _ _ _ (* NOTE Separate treatment? *)
      => CRcall
    | Return
      => CRret
    | Alloc _ _
    | Dealloc _ _
      => CRnone
    end.

  Definition op_callrets (os : option Operations) : CallRet :=
    match os with
    | None => CRnone
    | Some os' =>
        let crs := map op_callret os' in
        if seq.all (CallRet_eqb CRcall) crs then
          CRcall
        else if seq.all (CallRet_eqb CRret) crs then
          CRret
        else
          CRnone
    end.

  Definition CtxStateUpdate (m:MachineState) (cm:CodeMap_Impl) (prev:CtxState) : CtxState :=
    let '(dm, rts) := prev in
    match op_callrets ((CodeMap_fromImpl cm) (proj m PC)) with
    | CRcall => (* On a call, we check what the sealing convention wants to seal.
                      If a component is Sealed, it can't be sealed again under the new depth.
                      Everything else retains its old status, presumably Unsealed. In the standard,
                      stack pointer-based sealing convention, sc seals everything below the stack
                      pointer, but previously sealed frames retain their old owners. *)
      let d := length rts in
      let dm' := fun k =>
                    match k, dm k with
                    | Mem a, Unsealed =>
                      if sc m a
                      then Sealed d
                      else Unsealed
                    | Mem a, Sealed d' =>
                      Sealed d'
                    | _, _ => dm k
                    end in
      let rts' := rc m :: rts in
      (dm', rts')
    | CRret => (* On a return, we unseal everything sealed by the highest sealed depth. That will
                     always be one less than the current depth. Everything else remains. *)
      match popTo (fst (fst (step m))) rts with
      | Some rts' =>
(*        exception "BUT NOT HERE" *)
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
End TestSimpleDomain.

Module DLObs := DefaultLayout RISCVObs.
Module TSSRiscvDefault := TestSimpleDomain RISCVObs DLObs.

(* From StackSafety Require Import CeriseMachine CeriseLayout. *)
(* Module TSSCeriseDefault := TestSimpleDomain DefCerise CeriseLayout. *)
