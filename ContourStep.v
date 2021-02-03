Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* A Domain is an annotation on a component or set of components reflecting its
   relationship to the program state. Domains are nested, so a domain can be subsumed by
   a higher domain, and all of its components with it. For instance, a stack in a coroutine
   system has a domain containing all of the addresses in the stack's range, and the frames
   pushed on the stack each have their own, as described below. *)
Section DOMAIN_MODEL.

  (* First, an example of nested domains. Suppose we have a stack resulting from caller A
     calling callee B with a value v as an argument. The stack looks like this:
                     sp
     -----------------------------------------------
     | A's frame | v | Empty stack..................
     -----------------------------------------------
          a1      a2                a3

     B's frame is not yet allocated until it sets the stack pointer, but B
     has access to v and to everything above. So lets consider the status of
     addresses a1, a2, and a3 in the moment B gains control.

     a1 is in a frame that is currently inactive, but someday - after B returns - will
     again be active. a2 is also in an inactive frame, but it has been passed to B,
     so B should be allowed to use it. It will be active again after the
     return. We consider a1, by contrast, local. a3 is currently still active,
     and it will be active after the return, so it is active in two contexts.
     If B calls another function C without sharing a2, it should be inactive and
     local in that context.

     Now suppose that B calls a callee C that requires, as part of its calling convention,
     an array allocated at a fixed offset from the stack pointer that it will access as a
     pass-by-reference variable. We call that array arr, at address a3.

                                        sp
     -----------------------------------------------
     | A's frame | v | B's frame  | arr | Empty.....
     -----------------------------------------------
          a1      a2                a3

     Now what are the statuses of a1, a2, and a3? First, a1 is in a doubly inactive frame;
     it will take two returns before it's active again. It is also local. a2 is in an inactive frame,
     and in that frame it's local; but after a return it will still be inactive, but passed from its
     original owner, and after a further return it will once again be active.
     Finally a3 is in an inactive frame but shared, which is distinct from being passed because
     it is uninitialized.

     ===== On Sharing, Passing, and Protection =====
     Many systems provide some protection to shared data; the natural example
     is a capability system, in which a shared object is accessible only
     to a holder of a valid pointer, defined as one "descended" from the original.
     Our machinery will not track anything as detailed as pointer provenance, and cannot
     distinguish between legal and illegal uses of pointers to shared memory.

     Instead, our protection properties apply only to components that have not been shared.
     Once a component is shared, it is freely accessible, except in the narrow case of "passed"
     variables. A variable is "passed" when its address is only taken by the immediate callee,
     of its allocating function, and we assume that the compiler can guarantee that the pointer
     does not escape. This is the case for stack-allocated argument passing between subroutines.
     A passed component should be accessible in the immediate callee, then inaccessible in its nested calls.

     When a variable has its address taken in a context that may escape, it is considered "shared"
     and it is universally accessible until it is deallocated. A shared component has no protections
     unless proven separately. Systems can enforce safety of such components with capabilities or
     other techniques prove additional safety properties - in the case of capabilities, the property
     being memory safety.
   *)

  (* Defining domains: a domain carries sharing information about the objects in it. *)
  Inductive ObjectStatus :=
  | passed (* shared with the immediate callee only *)
  | shared (* shared widely *)
  | local  (* never shared *)
  .
 
  (* A stack domain is either active or inactive. An active domain may only contain other active
     domains, nested, so we treat such a nesting as a single object with a non-empty stack of object
     statuses. An inactive domain may contain other inactive domains, or active ones; it also tracks
     the sharing status of its objects. *)
  Inductive StackDomain :=
  | Inactive (os:ObjectStatus) (sd:StackDomain)
  | Active (os:ObjectStatus) (oss:list ObjectStatus) (* an active domain can only have active ones below it *)
  .

  (* Finally, the top-level domain type can make a component part of a stack (in which case
     it also needs to know which stack id it belongs to). It can also be code, in the heap, or
     a register. Later we can expand the definition of the heap to extend the model.
     Properly, stack sid sd denotes a domain at the coroutine level, but as it would be a
     single constructor it's folded in here. *)
  Inductive TopD :=
  | stack (sid:StackID) (sd:StackDomain)
  | code
  | heap
  | registers 
  .

  (* Finally we need a way to map components to the domain they belong to. *)
  Definition DomainMap := Component -> TopD.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  Variable cdm : CodeMap'.
  (* A stackmap defines the ranges of addresses each stack in a coroutine system may use.
     Note that this makes our maximum coroutine sizes static (theoretically at most two stacks
     get to be infinite, barring interleaving shenanigans.) The related findStack function maps
     an address to its stack, if any, whether or not it is in the allocated portion of the stack,
     and activeStack is a total function from states that determines which stack the stack pointer
     points to. *)
  Variable sm : StackMap.
  Variable pOf : MachineState -> PolicyState.

  Section WITH_FIXED_DOMAINMAP.

    Variable dm : DomainMap.
    (* Let's look at an example that isn't dynamic: coroutines without sharing.
       Intuitively, when a coroutine is active - determined by the stack pointer
       pointing somewhere in its stack - no other stack should be read or written.
       First lets talk about writing, and the integrity property.
       
       We call this an Ultra Eager property because it concerns the system's behavior
       at every step. At each step, if the active  *)
    Definition CoroutineIntNoShareUE : Prop :=
      forall minit m p dm m' p' o k sid sd,
        InTrace (m,p) (MPTraceOf (minit, pOf minit)) ->
        mpstep (m,p) = Some (m',p',o) ->
        dm k = stack sid sd ->
        activeStack sm m <> sid ->
        m k = m' k.

    (* We can do a similar Ultra Eager style property with confidentiality, and since we're
       not allowing sharing it is straightforward. But some preliminaries on confidentiality.
       Firstly: confidentiality is expressed in terms of "variant" states. A K-variant
       state of m is a state that agrees with m at every component not in the set K. It may also
       agree at some components in K. The intuition is that if the step from a state changes the
       state in the same way as the step from its K-variant, we can't tell from that step what
       value a component in K was, so K is secret. *)
    Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
      forall k, ~ K k -> m k = n k.

    (* "Changing the state in the same way" means that any component that changed is
       one trace ends with the same value in the other. *)
    Definition sameDifference (m m' n n' : MachineState) :=
      forall k,
        (m k <> m' k \/ n k <> n' k) ->
        m' k = n' k.

    (* Our Ultra Eager confidentiality property says that if we vary components outside
       the active stack at any point, our next step still produces the same output and
       changes the state in the same way. *)
    Definition CoroutineConfNoShareUE : Prop :=
      forall minit m p dm m' p' o sid sd n n',
        InTrace (m,p) (MPTraceOf (minit, pOf minit)) ->
        mpstep (m,p) = Some (m',p',o) ->
        activeStack sm m <> sid ->
        variantOf (fun k => dm k = stack sid sd) m n ->
        step n = (n',o) /\ (sameDifference m m' n n').

  End WITH_FIXED_DOMAINMAP.

  (* This is all well and good, but we want to deal with dynamic domains: objects becoming
     shared, and eventually protection of stack frames within each stack. So we need to
     introduce an initial domain map, an update function, and a way to map domainmaps
     onto existing MPTraces.

     The initial map is straightforward, and uses our code map and our stack map to arrange
     memory in code, stacks, and "heap" (which we don't really talk about yet.)*)
  Definition initD : DomainMap :=
    fun k =>
      match k with
      | Mem a =>
        if isCode' cdm a
        then code
        else match findStack sm a with
             | Some sid => stack sid (Active local [])
             | None => heap
             end
      | _ => registers
      end.

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
  
  Definition updateD (m:MachineState) (dm:DomainMap) : DomainMap :=
    match AnnotationOf cdm (m (Reg PC)) with
    | Some call => (* A call adjusts the domain map by marking the caller's frame "inactive" *)
                   (* and wrapping the remaining stack in a new instance of "active" *)
      fun k =>
        match k, dm k with
        | Mem a, stack sid (Active os oss) =>
          if sidEq (Some sid) (Some (activeStack sm m))
          then if wlt a (m (Reg SP))
               then stack sid (Inactive os (Active os oss))
               else stack sid (Active local (os::oss))
          else stack sid (Active os oss)
        | Mem a, stack sid (Inactive os sd) =>
          if sidEq (Some sid) (Some (activeStack sm m))
          then match os with
               | passed => stack sid (Inactive local (Inactive passed sd))
               | _ => stack sid (Inactive os (Inactive os sd))
               end
          else stack sid (Inactive os sd)
        | _,_ => dm k
        end
    | Some ret => (* A return unwraps the outermost domain of all components in the initial stack *)
      fun k =>
        match dm k with
        | stack sid (Inactive _ sd) =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then
            stack sid sd
          else dm k
        | stack sid (Active _ (os::oss)) => 
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then 
            stack sid (Active os oss)
          else dm k
        | _ => dm k
        end

    (* In Machine.v, the sharing annotation contains a partial function from a machine state m and
       an addresses a to a boolean, such that if it is defined on m and a, then a share step from
       state m shares (Mem a). If the bool is true, it is "passed," if false, "shared." *)
    | Some (share f) => (* A share applies only to an object in the active frame, and sets it to shared *)
      fun k =>
        match k with
        | Mem a =>
          match (f m) a, dm k with
          | Some true, stack sid (Active local oss) => stack sid (Active passed oss)
          | Some false, stack sid (Active local oss) => stack sid (Active shared oss)
          (* Do we need to change this all the way down the stack? I think we do. *)
          | Some false, stack sid (Inactive passed sd) => stack sid (Inactive shared sd)
          | _, _ => dm k
          end          
        | _ => dm k
        end
    | _ => dm
    end.

  Arguments WithContext {_}  _ _ _ _.
  Arguments ContextSegment {_} _ _ _.
  Arguments ObsOfMCP {_}.
  Arguments MCPState {_}.
  Arguments MCPTrace {_}.
  Arguments cstate {_}.
  
  (* With these tools, we can restate our Ultra Eager properties, but now with dynamic
     sharing. Note that for coroutines, "passed" objects are still private. *)
  Definition unshared (sd : StackDomain) : bool :=
    match sd with
    | Active shared _ => false
    | Active _ _ => true
    | Inactive shared _ => false
    | Inactive _ _ => true
    end.

  Definition sharedP sd := unshared sd = false.
  Definition unsharedP sd := unshared sd = true.
  
  Definition CoroutineIntUE : Prop :=
    forall minit MCP m dm p m' dm' p' k sid sd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,dm,p) (finished (m',dm',p'))) ->
      dm k = stack sid sd ->
      unsharedP sd ->
      activeStack sm m <> sid ->
      m k = m' k.

  Definition CoroutineConfUE : Prop :=
    forall minit MCP m cs p o m' cs' p' sid sd n n',
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP  (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      activeStack sm m <> sid ->
      variantOf (fun k => cs k = stack sid sd /\ unsharedP sd) m n ->
      step m = (m',o) ->
      step n = (n',o) /\ sameDifference m m' n n'.

  (* Now, within a given coroutine, it is really unnecessary to vary at each step,
     and in a testing setting this may be costly. We can instead vary at entry to
     a coroutine and check that the variation preserves behavior all the way to when
     the coroutine yields to another.

     This makes the property a bit more complicated, as the original trace might have
     one of three different qualities:

     1. it might end with a final state where the coroutine that can read a secret component is active
     2. it might end prematurely, due to a fail stop
     3. it might diverge and run forever without reaching the appropriate coroutine

     In case 1, the variant trace should reach a *convergent* state, one that is also in that coroutine.
        The traces should be observationally equivalent and the convergent states should be same-different.
     In case 2, the variant trace will not end, but its observations should be prefixed by the original.
     In case 3, the variant trace should be observationally equivalent to the original.

     We introduce a predicate Stuck that represents a trace that fail-stops before ever returning
     to the coroutine whose data is being protected. *)

  Definition Stuck (MPO : MPOTrace) : Prop :=
    exists m p o,
      Last MPO (m,p,o) ->
      mpstep (m,p) = None.

  (* Trace confidentiality is a property of a trace MCP with respect to a set of components
     Vary that are secret and should be varied, and a predicate on states of those that Converge. *)
  Definition TraceConfidentiality (MCP:MCPTrace)  (Vary:Component -> Prop) (Converge:MachineState -> Prop) : Prop :=
    forall m (cs:DomainMap) p n MO NO,
      head MCP = (m,cs,p) ->
      ObsOfMCP MCP MO -> (* We will mostly operate on the observation-annotated trace MO *)
      variantOf Vary m n ->
      PrefixUpTo (fun '(n',o) => Converge n') (RunOf n) NO ->
         (* Case 1 *)
      (forall mend p o,
          Last MO (mend,p,o) ->
          ~ Stuck MO ->
          exists nconv o',
            Last NO (nconv, o') /\
            ObsOfMP MO ~=_O ObsOfM NO /\
            sameDifference m mend n nconv)
      /\ (* Case 2 *)
      (Infinite MO ->
       ObsOfMP MO ~=_O ObsOfM NO)
      /\ (* Case 3 *)
      (Stuck MO ->
       ObsOfMP MO <=_O ObsOfM NO).

  (* We will use this definition of trace confidentiality in many contexts, not just coroutines!*)
  
  (* Coroutine confidentiality: for the set K of unshared components belonging to stack sid,
     for each trace segment where sid is inactive, trace confidentiality of K holds
     with convergence meaning that sid becomes active. *)
  Definition CoroutineConfEager : Prop :=
    forall minit MCP MCP' sid sd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      let K := fun k => cstate (head MCP') k = stack sid sd /\ unsharedP sd in
      let Converge := fun n => activeStack sm n = sid in
      TraceConfidentiality MCP' K Converge.

  (* Let's give a similar treatment to integrity. Suppose we wanted to test integrity
     of a system with coroutines. We don't actually need to check at every step that integrity
     is maintained; if we're considering a component that belongs to a coroutine, we need only
     check that from when that coroutine is inactive to when it becomes active again, the
     component remains unchanged. So we can examine a trace for integrity of a set of components: *)
  Definition TraceIntegrity (MCP:MCPTrace) (K:Component -> Prop) : Prop :=
    forall m (cs:DomainMap) p m' cs' p' k,
      K k ->
      head MCP = (m,cs,p) ->
      Last MCP (m',cs',p') ->
      m k = m' k.
  (* Note that if MCP is infinite, it fulfills trace integrity trivially. *)

  (* Now we have our eager, but not ultra-eager, coroutine integrity.
     It is similar to the confidentiality property. *)
  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP MCP' sid sd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      let K := fun k => cstate (head MCP') k = stack sid sd /\ unsharedP sd in
      TraceIntegrity MCP' K.
  
  (* Notice how coroutines have the nice property that we can always both read and write
     a component, or do neither. Confidentiality and integrity won't always line up in
     the future, even in more interesting coroutine models, and certainly
     not in our subroutine model. We introduce two pairs of security labels:
     - LC/HC: low and high confidentiality
     - LI/HI: low and high integrity

     So far we've seen stacks being (LC,LI) vs. (HC,HI). Code is (LC,HI).
     What kinds of components are (HC,LI)? Most notably ones that are uninitialized;
     initialization only having meaning inside of a stack. We'll get into that more,
     but first lets use labels with the ideas we've just
     seen to create a very general property. *)

  Definition SafetyProperty (Label : MachineState -> DomainMap -> Component -> Label)
             (SegmentProp : MachineState -> DomainMap -> Prop) :=
    forall minit MCP MCP' m dm p,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment SegmentProp MCP MCP' ->
      head MCP' = (m,dm,p) ->
      let ProtectedK := (fun k => integrityOf (Label m dm k) = HI) in
      TraceIntegrity MCP ProtectedK /\
      let VariedK := (fun k => confidentialityOf (Label m dm k) = HC) in
      let Converged := (fun m => ~ SegmentProp m dm) in
      TraceConfidentiality MCP VariedK Converged.

  (* We can implement code safety by mapping code components to (LC,HI)...*)
  Definition CodeContour (m:MachineState) (dm:DomainMap) (k:Component) :=
    match dm k with
    | code => (LC,HI)
    | _ => (LC,LI)
    end.

  (* ...and taking all segments of length two, since code *must* be treated ultra-eagerly.*)
  Definition CodeSafety : Prop :=
    SafetyProperty CodeContour (fun _ _ => False).

  (* We can implement coroutine safety by combining the same integrity and
     confidentiality concepts as above into labels... *)
  Definition CoroutineContour (m:MachineState) (dm:DomainMap) (k:Component) :=
    match dm k with
    | stack sid sd =>
      if sidEq (Some sid) (Some (activeStack sm m)) || negb (unshared sd)
      then (LC,LI)
      else (HC,HI)
    | _ => (LC, LI)
    end.

  (* ... and taking all segments where a stack *isn't* active. *)
  Definition CoroutineSafety : Prop :=
    forall sid,
      SafetyProperty CoroutineContour (fun m _ => activeStack sm m <> sid).

  (* Now for subroutines! We will lean heavily on already defined machinery.
     When we enter a new call, if a component is in the active frame, it is to be treated
     as uninitialized: (HC,LI).
     If it is inactive and passed or shared, it is (LC,LI).
     Inactive, local components are (HC,HI).
     At some point it may be useful to distinguish a read-only sharing that is (LC,HI).*)
  Definition SubroutineContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match k with
      | Mem a =>
        match dm (Mem a) with
        | stack _ (Active _ _) => (HC,LI)
        | stack _ (Inactive local _) => (HC,HI)
        | stack _ (Inactive _ _) => (LC,LI)
        | _ => (LC,LI)
        end
      | _ => (LC,LI)
      end.

  Fixpoint depth (sd:StackDomain) : nat :=
    match sd with
    | Active os oss => 1+(length oss)
    | Inactive os sd => 1+(depth sd)
    end.

  (* Stack safety takes all stacks s and stack depths d, and takes the segment of execution where,
     the stack of s has at least d frames, as indicated by any component having a domain "stack s sd"
     with sd of depth d. These segments represent function activations, possibly with nested calls that
     must obey their caller's trace properties as well as their own. *)
  Definition StackSafety : Prop :=
    forall s d,
      SafetyProperty SubroutineContour (fun m dm => exists k sd, dm k = stack s sd /\ depth sd >= d).

  (* There is a version of stack safety in which the residual data of a call should not
     be accessible after it returns. In this variant we would need confidentiality to
     apply to subtraces where sd has exactly depth d, i.e. separate subtraces within an activations.
     It might make the most sense for that to be a separate property. *)

  (****** Lazy Properties ******)
  
  (* Some enforcement methods do not actually completely enforce our safety properties,
     but instead guarantee that illegal reads and writes are caught after the fact, before
     they are able to affect the observable behavior of the program. In particular, lazy
     policies allow writes to a high-integrity location, but "taint" it so that a fail-stop
     will occur on read. Effectively, it becomes high-confidentiality, permanently, once
     the write occurs. This is represented by establishing that if a component has changed at
     the final state, then any k-variant of that final state must have the same or prefixed
     behavior (where prefix indicates that the system fail-stopped later.) *)
  
  Definition TraceIntegrityLazy (MCP:MCPTrace) (Protected:Component -> Prop) : Prop :=
    forall m (dm dm':DomainMap) p m' p' k,
      Protected k ->
      head MCP = (m,dm,p) ->
      Last MCP (m',dm',p') ->
      m k <> m' k ->  
      forall m'', variantOf Protected m' m'' ->
                  ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf  m'').


  (* We might instead reset k to what it was initially. *)
  Definition RollbackInt (k:Component) (Mstart Mend : MachineState) : MachineState :=
    fun k0 => if keqb k k0 then Mstart k0 else Mend k0.

  (* This produces an even weaker property, in which it is permissible to
     alter k and even to later access it, as long as the remaining execution 
     is not observably changed. Such scenarios are easy to construct relative 
     to a well-understood program, such as multiplying a value that is always
     treated as a boolean by a nonzero constant, but are difficult to generalize. *)
  Definition TraceIntegrityLazier (MCP:MCPTrace) (Protected:Component -> Prop) : Prop :=
    forall m (dm dm':DomainMap) p m' p' k,
      Protected k ->
      head MCP = (m,dm,p) ->
      Last MCP (m',dm',p') ->
      ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf (RollbackInt k m m')).

  (* If we substitute one of these properties for TraceIntegrity in the general safety
     property, we have lazy versions of each of our safety properties. *)

  (* Stop here for Thursday demo. *)
  (* ********************* Control Flow with Coroutines ******************** *)

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
    forall s d minit MCP MCP' m c p m' c' p',
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun m '(dm,d') => d' >= d) MCP MCP' ->
      head MCP' = (m,c,p) ->
      Last MCP' (m',c',p') ->
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
