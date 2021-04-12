Require Import List.
Import ListNotations.
Require Import Bool.
Require Import ZArith.
Require Import Nat.


From StackSafety Require Import Trace MachineImpl ObsTrace.

  Section DOMAIN_MODEL.

  (* In general, a domain is a coherent logical division of the state (both memory and registers)
     that has meaning in one or more of our security properties. Domain models will get
     complicated, but let's start with a simple one: the simple stack, in which we have 
     subroutines with no arguments passed on the stack and no sharing.

     Here the state is divided into "Outside" - anything that isn't part of the
     stack - and Sealed and Unsealed portions of the stack. Sealed and Unsealed
     can be thought of as a contract between the active function and its caller(s).

     The first contract of stack safety is: the caller identifies memory that
     it will need after the call, and that memory is expected to remain unchanged.
     This is, in security terms, integrity - the callee cannot subvert the caller's
     Sealed data.

     The second contract of stack safety is that given fixed arguments, the callee
     always behaves the same regardless of the calling context. In the simple stack,
     all arguments are Outside the stack itself. In security terms, this is confidentiality,
     and we express it as a noninterference property. We will come back to it after
     the domain model, which is only relevant to integrity.

     For example, consider a function A that calls another function, B. At the
     point of entry to B, A has identified some memory that it expects to remain
     unchanged - in this case, everything below the stack pointer, sp:
                                 sp
     +======================================
     | Other memory | A's frame  | Available
     +======================================
       Outside        Sealed (0)   Unsealed

     The Sealed mark on A's frame is annotated with the depth of the call that sealed it,
     in this case 0.

     B can use unsealed memory however it likes without violating A's contract. It can
     also modify other memory and registers without violating stack safety. When it makes
     a call, however, say to another function C, it may seal some memory for its own
     future use after the return.

                                             sp
     +==================================================
     | Other memory | A's frame  | B's frame | Available
     +==================================================
       Outside        Sealed (0)   Sealed (1)  Unsealed

     When C returns, B's frame will be unsealed. Perhaps B will deallocate some data,
     then call another function D; it will reseal the data it still needs, and only that data.

                                          sp
     +===============================================
     | Other memory | A's frame  | B's fr | Available
     +===============================================
            O          S (0)       S (1)     U
 *)

  Inductive StackDomain :=
  | Sealed (d:nat)
  | Unsealed
  | Outside
  .


  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  (* The Code and Stack maps tell us about the initial layout of memory, as determined
     by the compiler. They will help us build our initial DomainMap and identify
     calls and returns in the code, in the form of annotations. *)

  (* sm is a simplified stack map that merely identifies whether an address is in the stack *)
  Variable sm : Addr -> bool.

  (* The stack pointer is by far the most typical, but technically other mechanisms could be
     used to seal addresses. We assume that which addresses are being sealed is deducible from
     the machine state (e.g., by comparing them to the stack pointer)
     and attempting to re-seal already sealed addresses is a no-op. *)
  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Definition sc : SealingConvention :=
    fun m a => wlt a (proj m (Reg SP)).

  (* Likewise, we need to describe what it means to return properly from a call. We parameterize
     this as well, but the standard of course is that the stack pointer must match the original
     call point and the program counter should be one instruction (four cell) later. *)
  Definition ReturnConvention : Type := MachineState -> MachineState -> bool.
  Definition rc : ReturnConvention :=
    fun m1 m2 => weq (proj m1 (Reg SP)) (proj m2 (Reg SP)) &&
                 weq (proj m1 PC) (wplus (proj m2 PC) 4).

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
  
  Definition context : Type := DomainMap * ReturnTargets.

  (* For the initial context, we construct a domain map that maps the stack to Unsealed
     and everything else to Outside. The stack depth is 0. *)
  Definition initC (m:MachineState) : context :=
    let dm := fun k =>
                match k with
                | Mem a =>
                  if sm a
                  then Unsealed
                  else Outside
                | _ => Outside
                end in
    (dm, []).

  (* Our update function checks an "annotation" on the code being executed.
     Annotations are defined in Machine.v, and the ones that matter here are call and return.
     The annotations are carried by a Code Map, which also tells us which addresses are code. *)
  Variable cdm : CodeMap.
  
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, rts) := prev in
    match AnnotationOf cdm (proj m PC) with
    | Some call => (* On a call, we check what the sealing convention wants to seal.
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
    | Some ret => (* On a return, we unseal everything sealed by the highest sealed depth. That will
                     always be one less than the current depth. Everything else remains. *)
      match popTo (fst (step m)) rts with
      | Some rts' =>
        let d := length rts' in
        let dm' := fun k =>
                     match dm k with
                     | Sealed d' =>
                       if d <=? d'
                       then Unsealed
                       else Sealed d'
                     | _ => dm k
                     end in
        (dm', rts')
      | _ => (dm, rts)
      end
    | _ => (dm, rts)
    end.

  (* Now it's quite simple to define a "stepwise" integrity property:
     if we run from any initial state, updating the context as above, then
     at any particular state where a component k is in an Sealed domain,
     k has the same value in the following state (if any.) We term this property
     ultra eager because it "checks" at each step that components that are inaccessible
     don't change, the most frequently it is possible to check. *)
  Definition SimpleStackIntegrityStep : Prop :=
    forall k d m c p m' p' c' o,
      Reachable updateC initC (m,p,c) ->
      mpcstep updateC (m,p,c) = Some (m',p',c',o) ->
      fst c k = Sealed d ->
      proj m k = proj m' k.

  (* TODO: Sean, check this corresponds? *)
  Definition SimpleStackIntegrityStepP fuel m p c :=
    let fix aux fuel m p c :=
        match fuel with
        | O => true
        | S fuel' => 
          match mpcstep updateC (m,p,c) with
          | None => true (* right? *)
          | Some (m', p', c', o) =>
            andb
              (List.forallb (fun k =>
                            match fst c k with
                            | Sealed _ =>
                              Z.eqb (proj m k) (proj m' k)
                            | _ => true
                            end)
                            (getComponents m'))
              (aux fuel' m' p' c')
          end
        end in
    aux fuel m p c.
  
  (* In addition to integrity, we have a confidentiality property. Consider in our
     example when B called C and then D. Suppose that B has some secret data, say a capability on some
     system critical resource, that A, C and D should not access. Clearly, D should not read
     B's sealed memory to find it. But it is possible that it could be left behind in the
     memory B deallocated, so that to D, it is not sealed. So we could use "sealedness" to determine
     when something should be confidential, but it is not sufficient. Secrets could be left behind
     anywhere in the stack, so we protect the entire stack from being read until it's initialized.

     Confidentiality is expressed in terms of "variant" states. A K-variant
     state of m is a state that agrees with m at every component not in the set K. It may also
     agree at some components in K. The intuition is that if the step from a state changes the
     state in the same way as the step from its K-variant, we can't tell from that step what
     value a component in K was, so K is secret. *)
  Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> proj m k = proj n k.
  
  (* The idea is that when variant states step, the resulting states should agree on any component
     that changed. *)
  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (proj m k <> proj m' k \/ proj n k <> proj n' k) ->
      proj m' k = proj n' k.

  (* When we have same-difference, we can talk about traces being in lockstep. Intuitively
     what this means is that, whatever the relationship between their initial states,
     their states evolve in concert according to same-difference. *)
  Inductive Lockstep : @MPCTrace context -> @MPCTrace context -> Prop :=
  | bothDone : forall m p c n,
      Lockstep (finished (m,p,c)) (finished (n,p,c))
  | bothStep : forall m p c m' n n' M N,
      mstate (head M) = m' ->
      mstate (head N) = n' ->
      sameDifference m m' n n' ->
      Lockstep M N ->
      Lockstep (notfinished (m,p,c) M) (notfinished (n,p,c) N)
  .

  (* Once again, we take adjacent pairs of states in the trace from an arbitrary
     start state and check that a property holds between them. In this case, that
     in any K-variant of the first state where K is the set of components that are
     Sealed in that state, the step has the same observable behavior and makes
     the same changes to state. *)
  Definition SimpleStackConfidentialityStep : Prop :=
    forall d m p c n M N,
      let P := fun '(_,_,c) => length (snd c) > d in
      ReachableSegment updateC initC P M ->
      head M = (m,p,c) ->
      variantOf (fun k => fst c k = Sealed d) m n ->
      MPCTraceToWhen updateC P (n,p,c) N ->
      Lockstep M N.
  
  (* ***** Control Flow Properties ***** *)

  (* Do we even value control separation? *)
(*    Definition ControlSeparation : Prop :=
    forall minit m1 p1 m2 p2 o f1 f2 ann1 ann2,
      InTrace (m1,p1) (MPTraceOf (minit, pOf minit)) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (proj m1  PC) = inFun f1 ann1 ->
      cdm (proj m2  PC) = inFun f2 ann2 ->
      f1 <> f2 ->
      AnnotationOf cdm (proj m1 PC) = Some call \/
      AnnotationOf cdm (proj m1 PC) = Some ret. *)

  Definition ReturnIntegrity : Prop :=
    forall mpc mpc' o,
      Reachable updateC initC mpc ->
      mpcstep updateC mpc = Some (mpc',o) ->
      AnnotationOf cdm (proj (mstate mpc) PC) = Some ret ->
      exists rt rts,
        snd (cstate mpc) = rt :: rts /\
        snd (cstate mpc') = rts.

(* Think about how/whether we deal with entries here.

  Variable em:EntryMap.
  
  Definition EntryIntegrity : Prop :=
  forall mpc1 mpc2 o,
    Reachable updateC initC mpc1 ->
    mpcstep updateC mpc1 = Some (mpc2,o) ->
    AnnotationOf cdm (proj (mstate mpc1) PC) = Some call ->
    em (proj (mstate mpc2) PC) = true. *)

  Definition WellBracketedControlFlow  : Prop :=
    (*ControlSeparation /\*)
    (* EntryIntegrity /\*)
    ReturnIntegrity.
  
  (* Continue to SubroutineShare.v, where we enhance the model with sharing between calls. *)

End WITH_MAPS.

