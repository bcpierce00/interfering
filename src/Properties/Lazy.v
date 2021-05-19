Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.

From StackSafety Require Import Trace Machine ObsTrace TraceProperties Coroutine.

(* A lazy integrity property is one that doesn't care directly about the state
   of the machine, but focuses on whether an adversary can cause changes in the
   visible behavior of another domain. We offer two such properties. The first
   attempts to consider, for any changes to sealed components, a hypothetical
   world in which they do not change.

   The second is slightly stronger, and treats a change to sealed state as a
   secret that should never become observable at all. Its strength avoids certain
   cases where the first property has difficult intuition.
 *)

  Section LAZY_TRACE_PROPS.

    Variable context : Type.
    Variable updateC : MachineState -> context -> context.

    Definition rollback (m m':MachineState) (K : Component -> Prop) (m'': MachineState) : Prop :=
      forall k,
        K k ->
        proj m k <> proj m' k ->
        proj m'' k = proj m k /\
        (K k \/ proj m k = proj m' k) ->
        proj m'' k = proj m' k.

    Definition TraceIntegrityLaziest
               (K : Component -> Prop)
               (MPC:@MPCTrace context) : Prop :=
      forall m p c m' Om On K,
        Last MPC (m,p,c) ->
        rollback (mstate (head MPC)) m K m' ->
        ObsOfMPC updateC (MPCTraceOf updateC (m,p,c)) Om ->
        ObsOfMPC updateC (MPCTraceOf updateC (m',p,c)) On ->
        Om ~=_O On.

    (* The second property identifies the subset of protected components that
       changed between the beginning and the end of the trace. The property holds
       if that subset remains confidential permanently, defined in terms of trace
       confidentiality holding on the trace from the final state.*)
    Definition TraceIntegrityLazy
               (K : Component -> Prop)
               (MPC:@MPCTrace context) : Prop :=
      forall m p c,
        Last MPC (m,p,c) ->
        let K' := fun k => K k /\ proj (mstate (head MPC)) k <> proj (mstate (m,p,c)) k in
        let P := fun _ => False in
        TraceConfidentialityEager updateC K' P (MPCTraceOf updateC (m,p,c)).

    (* Distinguishing example
       f() {
         int x = 0;
         g();
         if(x)
           print x;
         else
           print 1;
       }

       g() {
         x = 1 // through arithmetic from the stack pointer, set x to 1
       }
     *)

    (* Policy-aware (testable) property *)
    Variable DeadCrit : MPState -> Component -> Prop.
    Definition ReallyDead (DeadCrit : MPState -> Component -> Prop) : Prop :=
      forall mp c,
        let K := fun k => DeadCrit mp k in
        let P := fun _ => False in
        TraceConfidentialityEager updateC K P (MPCTraceOf updateC (mp,c)).

    Definition IntegrityOrDeath
               (DeadCrit : MPState -> Component -> Prop)
               (K : Component -> Prop)
               (MPC:@MPCTrace context) : Prop :=
      forall m p c k,
        Last MPC (m,p,c) ->
        K k ->
        proj (mstate (head MPC)) k = proj (mstate (m,p,c)) k \/ DeadCrit (m,p) k.

    Theorem TraceIntegrityDeadLazy :
      forall K MPC,
        ReallyDead DeadCrit ->
        IntegrityOrDeath DeadCrit K MPC ->
        TraceIntegrityLazy K MPC.
    Proof.
      unfold TraceIntegrityLazy.
      unfold ReallyDead.
      unfold TraceConfidentialityEager.
      intros. specialize H with (m,p) MPC0 m0 c0 p0 n N Om On.
      apply (H c H2); auto.
      unfold variantOf. intros.
      apply H3. intro. destruct H8.
      unfold IntegrityOrDeath in H0.
      specialize H0 with m p c k. apply H0 in H1; auto. destruct H1; auto.
    Qed.

    Definition UltraDead (DeadCrit : MPState -> Component -> Prop) : Prop :=
      forall m n p m' n' p' p'' o o',
        let K := fun k => DeadCrit (m,p) k in
        variantOf K m n ->
        mpstep (m,p) = Some (m',p',o) ->
        mpstep (n,p) = Some (n',p'',o') ->
        forall k,
          proj m' k <> proj n' k ->
          DeadCrit (m',p') k /\ DeadCrit (n',p') k.

    Theorem UltraDeadIsReallyDead :
      UltraDead DeadCrit -> ReallyDead DeadCrit.
    Proof.
      unfold UltraDead. unfold ReallyDead.
      unfold TraceConfidentialityEager. intros.
    Admitted.
      
      
  End LAZY_TRACE_PROPS.

  (* We add coroutines with multiple stacks, defined with static extents (see Machine.v).
     Our domain model uses the same stack domain as previous, but now a top-level domain
     combines a stack identity and the domains of that stack. Outside is now a top domain. *)
  Section DOMAIN_MODEL.

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

    (* We will additionally track the depths of all the stack simultaneously. *)
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

    Variable cdm : CodeMap.
    Variable sm : StackMap.

    Definition SealingConvention : Type := MachineState -> Addr -> bool.
    Variable sc : SealingConvention.

    Definition context : Type := DomainMap * DepthMap.
  
    Definition initC : DomainMap * DepthMap :=
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
      (dm,initDepM).
  
    (* Once again we need an update function for out context. Note that yields don't
       actually change the domain map, as they don't change which addresses belong to which
       stacks. So we still only consider sharing, calls, and returns. *)
    Definition updateC (m:MachineState) (prev:context) :
      context :=
      let '(dm, depm) := prev in
      match activeStack sm m with
      | None => prev (* Shouldn't happen *)
      | Some sid => 
        let d := depm sid in
        match AnnotationOf cdm (proj m PC) with
        | Some (share f) =>
          let dm' := fun k =>
                       match k with
                       | Mem a =>
                         match f m a, dm k with
                         | Some true, Instack sid' Unsealed =>
                           if stack_eqb sid sid' 
                           then Instack sid (Passed d)
                           else dm k
                         | Some false, Instack sid' Unsealed =>
                           if stack_eqb sid sid' 
                           then Instack sid (Shared d)
                           else dm k
                         | _, _ => dm k
                         end
                       | _ => dm k
                       end in
          (dm', depm)
        | Some call =>
          let dm' := fun k =>
                       match k, dm k with                      
                       | _, Instack sid' (Sealed d) => Instack sid' (Sealed d)
                       | _, Outside => Outside
                       | Mem a, Instack sid' _ =>
                         if sc m a && stack_eqb sid sid'
                         then Instack sid (Sealed d)
                         else Instack sid Unsealed (* If addresses are marked to be shared but the sealing convention
                                                      wants them unsealed, the sealing convention takes precedence *)
                       | _, _ => dm k
                       end in
          (dm', push depm sid)
        | Some ret => 
          let dm' := fun k =>
                       match dm k with
                       | Instack sid' (Sealed d') =>
                         if (d-1 =? d') && stack_eqb sid sid'
                         then Instack sid Unsealed
                         else dm k
                       | Instack sid' (Passed d') =>
                         if (d-1 =? d') && stack_eqb sid sid'
                         then Instack sid Unsealed
                         else dm k
                       | Instack sid' (Shared d') =>
                         if (d =? d') && stack_eqb sid sid'
                         then Instack sid Unsealed
                         else dm k
                       | _ => dm k
                       end in
          (dm', pop depm sid)
        | _ => (dm, depm)
        end
      end.

    Definition StackInaccessible (c:context) (k:Component) : Prop :=
      exists sid d,
        fst c k = Instack sid (Sealed d) \/
        (fst c k = Instack sid (Passed d) /\ d < (snd c sid)-1).
    
    (* We split up our inaccessibility criterion into stack and coroutine variations.
       The coroutine version takes the active stack, and prohibits accessing other stacks
       except for shared objects. *)
    Definition CoroutineInaccessible (c:context) (sid:StackID) (k:Component) : Prop :=
      forall sid' sd d,
        fst c k = Instack sid' sd ->
        (sid <> sid /\ sd <> Shared d).

    Definition StackIntegrityUE : Prop :=
      forall k m c p m' p' c' o,
        Reachable updateC initC (m,p,c) ->
        mpcstep updateC (m,p,c) = Some (m',p',c',o) ->
        StackInaccessible c k ->
        proj m k = proj m' k.
  
    Definition CoroutineIntegrityUE : Prop :=
      forall sid k m c p m' p' c' o,
        Reachable updateC initC (m,p,c) ->
        mpcstep updateC (m,p,c) = Some (m',p',c',o) ->
        CoroutineInaccessible c sid k ->
        proj m k = proj m' k.
    
    (* We can actually do ultra eager confidentiality for coroutines without any more complexity,
       because coroutine properties don't care about allocation and initialization. That only comes
       when subroutine properties are layered in. *)
    Definition SealedConfidentialityUE : Prop :=
      forall sid m p c m' p' c' n o n' p'' c'' o',
        Reachable updateC initC (m,p,c) ->
        mpcstep updateC (m,p,c) = Some (m',p',c',o) ->
        variantOf (fun k => CoroutineInaccessible c sid k) m n ->
        mpcstep updateC (n,p,c) = Some (n',p'',c'',o') ->
        sameDifference m m' n n' /\ p' = p'' /\ o = o'.

    Definition StackIntegrityEager : Prop :=
      forall MCP sid d,
        ReachableSegment updateC initC (fun '(m,p,c) => snd c sid >= d) MCP ->
        TraceIntegrityEager (StackInaccessible (cstate (head MCP))) MCP.

    Definition CoroutineIntegrityEager : Prop :=
      forall MCP sid,
        ReachableSegment updateC initC (fun '(m,p,c) => activeStack sm m = Some sid) MCP ->
        TraceIntegrityEager (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) MCP.
    
    Definition StackConfidentialityEager : Prop :=
      forall sid MCP d m dm depm p,
        let P := (fun '(m,p,c) => snd c sid >= d) in
        let K := (fun k => StackInaccessible (cstate (head MCP)) k \/
                           fst (cstate (head MCP)) k = Instack sid Unsealed) in
        ReachableSegment updateC initC P MCP ->
        head MCP = (m,p,(dm,depm)) ->
        TraceConfidentialityEager updateC K P MCP.
  
    Definition CoroutineConfidentialityEager : Prop :=
      forall MCP sid,
        let P := (fun '(m,p,c) => activeStack sm m = Some sid) in
        let K := (fun k => CoroutineInaccessible (cstate (head MCP)) sid k) in
        ReachableSegment updateC initC P MCP ->
        TraceConfidentialityEager updateC K P MCP.

    (* ***** Control Flow Properties ***** *)


    (* Finally, we also need to consider control flow properties. These are included here because
       they don't really change in interesting ways between the different models. *)
  
    (*Definition ControlSeparation : Prop :=
      forall minit m1 p1 m2 p2 o f1 f2 ann1 ann2,
      InTrace (m1,p1) (MPTraceOf (minit, pOf minit)) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (proj m1 PC) = inFun f1 ann1 ->
      cdm (proj m2 PC) = inFun f2 ann2 ->
      f1 <> f2 ->
      AnnotationOf cdm (proj m1  PC) = Some call \/
      AnnotationOf cdm (proj m1  PC) = Some ret \/
      AnnotationOf cdm (proj m1  PC) = Some yield. *)

    Definition YieldBackIntegrity : Prop :=
      forall mpc1 mpc2,
        let P := (fun mpc => sm (proj (mstate mpc1) (Reg SP)) = sm (proj (mstate mpc) (Reg SP))) in
        Reachable updateC initC mpc1 ->
        AnnotationOf cdm (proj (mstate mpc1) PC) = Some yield ->
        StepsToWhen updateC P mpc1 mpc2 ->
        justRet (mstate mpc1) (mstate mpc2).

    Definition ReturnIntegrity : Prop :=
      forall d sid MCP m c p m' c' p',
        let P := fun '(m,p,c) => activeStack sm m = Some sid /\ (snd c) sid >= d in
        ReachableSegment updateC initC P MCP ->
        head MCP = (m,c,p) ->
        Last MCP (m',c',p') ->
        justRet m m'.
  
    Variable em:EntryMap.

    Definition EntryIntegrity : Prop :=
      forall mpc1 mpc2 o,
        Reachable updateC initC mpc1 ->
        mpcstep updateC mpc1 = Some (mpc2,o) ->
        AnnotationOf cdm (proj (mstate mpc1) PC) = Some call ->
        em (proj (mstate mpc2) PC) = true.

    Definition WellStructuredControlFlow  : Prop :=
      (*ControlSeparation /\ *)
      ReturnIntegrity /\
      YieldBackIntegrity /\
      EntryIntegrity.

  End WITH_MAPS.
