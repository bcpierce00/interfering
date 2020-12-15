Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Omega.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

(* A Domain is a logical unit associated with a collection of components, and can be thought of as the
   owner of a component. Domains are nested, so a domain can belong to a higher domain, and all of its
   components with it. For instance, a component in the stack frame for a caller belongs to the active
   frame for that caller as well as the sealed portion of the stack for its callee, and additionally
   belongs to the domain of that stack as a whole (in a multi-stack system). *)
Section DOMAIN_MODEL.

  (* First, an example of domains. Suppose we have a stack resulting from caller A
     calling callee B with a value v as an argument. The stack looks like this:
                     sp
     -----------------------------------------------
     | A's frame | v | Empty stack..................
     -----------------------------------------------
          a1      a2                a3

     B's frame is not yet allocated until it sets the stack pointer, but B
     has access to v and to everything above. So lets consider the status of
     addresses a1, a2, and a3.

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
     Many systems provide a degree of protection to shared data; the natural example
     is a capability system, in which an object gets shared down-stack is accessible only
     to a holder of a valid pointer to it, with validity defined in terms of the history
     of the pointer. Our machinery for defining properties does not and will not track anything
     as detailed as pointer provenance, and cannot distinguish between legal and illegal
     uses of pointers to shared memory.

     Instead, our stack protection properties apply only to components that have not been shared.
     Once a component is shared, as long as it is shared, it is freely accessible.
     The length of sharing is the difference between what we call "shared" vs "passed" variables.

     A variable is "passed" when its address is only taken by the immediate callee, and we assume
     that the compiler can guarantee that the address does not escape. This is the case for
     stack-allocated argument passing. A passed component should be accessible in the immediate callee,
     then inaccessible in its nested calls - they shouldn't know exactly where it is, let alone
     be able to access it.

     When a variable has its address taken in a context that may escape, it is considered "shared"
     and it is accessible by everyone until it is deallocated. A shared component has no protections
     except those proven separately. I recommend that systems that enforce safety of such components
     with capabilities or other techniques prove additional safety properties - in the case of
     capabilities, memory safety.

     ====== On the term "domain" ======
     In security literature, we often see the notion of units of identity that have common
     security properties referred to as domains. Protection domains associated with a process,
     for instance. Often we give them names. Domains may have permissions on objects, with
     objects possibly shared between several domains, but we don't usually see this idea of domains
     being nested. But if we think of a function activation as a domain, its permissions
     are in some sense dependent on those of the caller's domain. This nesting renders multi-ownership
     unnecessary.
     
     If we were to give domains unique names, we would identify stack domains by distinct
     activations of each function (perhaps using a counter). But for the purposes of the property
     we don't need them to be unique, just to capture the appropriate status of each component
     relative to a given context and any contexts that will be returned to later.
   *)

  (* Objects don't get their own "domains," but within a domain some components might be shared or passed. *)
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
  (* Now we describe how components are assigned to domains with an initial
     domain map and a update function, given our initial program maps *)

  Variable cdm : CodeMap'.
  (* A stackmap defines the ranges of addresses each stack in a coroutine system may use.
     Note that this makes our maximum coroutine sizes static (theoretically at most two stacks
     get to be infinite, barring interleaving shenanigans.) The related findStack function maps
     an address to its stack, if any, whether or not it is in the allocated portion of the stack. *)
  Variable sm : StackMap.
  Variable pOf : MachineState -> PolicyState.
  
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

  (* Our update function checks the annotation on the code being executed.
     Annotations are defined in Machine.v as an alternative to a million different
     maps, and the ones that matter are call, return, yield, and share.

     Annotations are given by the compiler. We assume that the compiler can tell us
     which instructions represent calls, returns, and yields. Shares are more complicated;
     the compiler cannot tell us which component(s) are being shared. Instead it can identify
     another component, typically a register, that holds the target of the share.

     For example, suppose that a caller is sharing an address as an argument to its callee.
     It executes a store instruction that the compiler identifies as a share; the target of
     the share is the address to which the argument is being stored, held within the appropriate
     register.

     Note that yields don't actually change the contour state, as they don't change which
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

    (* Much needs to be said about sharing. In Machine.v, the sharing annotation contains a partial function
       from a machine state m and an addresses a to a boolean, such that if it is defined on m and a,
       then 

       Our general model is that the compiler will associate instructions with different conventions for
       sharing depending on the role of the object being shared. Consider one typical sharing convention,
       the passing of an argument:
       - the caller raises the stack pointer to allocate the argument
       - it computes the address of the argument in register r
       - then it stores the argument value to that address
         -- the address being shared is found in r
         -- only that address is shared, and it has been initialized
         -- so, the compiler annotates this write as (share r (fun w => [w,true]))

       Lets think about a scenario where a caller allocates a dynamic array for the callee to fill:
       - the caller computes the size of the array in r
       - then it increases the stack pointer by that much
         -- the shared object is of size r and ends at the stack pointer
         -- it is not initialized
         -- so, the compiler annotates this write as (share r (fun w => {a,false | SP-w <= a < SP}))
       Note that this convention assumes the array will be secret
     If we wanted to describe a dynamic array based at an arbitrary register -- then we would need r1,r2 ... 
     Seems better to pass the entire state, or at least the entire register set.
     *)
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

  (* APT: I think we should explore enriching the set of annotations to include, for example, initializing writes
        that would change a location from HC to LC. *)
  (* SNA: this would be most useful with shared memory, but I am leaning toward making that always LC. *)
  
  (* Eventually we will see a unified model of integrity and confidentiality using
     "contours" - generic permissions structures derived from domain maps - but first
     we can look at a simple example of how to build a safety property on this model:
     an ad-hoc code safety property. Note that this property gets to be simple because
     the code domain is static; on the way to stack safety we will add
     quite a bit more machinery to deal with changing domains.

     Code safety says that starting from any initial state, between each adjacent
     pair of states mp and mp' in the program trace, all components in the code domain
     are unchanged. *)
  Definition AdHocCodeSafety : Prop :=
    forall minit mp mp' o k,
      InTrace mp (MPTraceOf (minit, pOf minit)) ->
      (initD k) = code ->
      mpstep mp = Some (mp',o) ->
      (ms mp) k = (ms mp') k.  
  
  (* Now suppose that we had, in our formalization, the ability to expand the code
     domain to reflect adding some new code to the system. We might well want such
     a feature some day. We will need to deal with the way domains change over time.
APT: Not sure this is the best example for introducing context state, since your updateD doesn't in fact ever change the code region.
SNA: Good point, this progression needs some work.
     Let's introduce some machinery for carring extra state along with an MPTrace. *)
  Section WITH_STATE.
(* APT: I haven't reviewed this carefully yet. *)
    Variable ContextState : Type.
    Variable ContextStateUpdate : MachineState -> ContextState -> ContextState.

    Definition MCPState : Type := MachineState * ContextState * PolicyState.
    Definition MCPTrace := TraceOf MCPState.
    Definition cstate : MCPState -> ContextState := fun '(m,cs,p) => cs.
    Definition MPOTrace := MPTrace'.

    (* WithContour relates an MPTrace to its MCPTrace given an initial contour state cs.
       A finished trace (m,p) is related to (m,cs,p).
       We relate a trace (notfinished (m,p) MP) to (notfinished (m,cs,p) MCP),
       where MP relates to MCP given cs' produced by ContextStateUpdate. Additionally,
       the relation requires that MP begin with m' and p' produced by mpstep (m,p),
       so that only MPTraces produced by the step function relate to any MCPTrace *)
    Inductive WithContext (cs:ContextState) : MPTrace -> MCPTrace -> Prop :=
    | WCFinished : forall m p,
        WithContext cs (finished (m,p)) (finished (m,cs,p))
    | WCNotfinished : forall m p cs' m' p' o MP MCP,
        mpstep (m,p) = Some (m',p',o) ->
        ContextStateUpdate m cs = cs' ->
        WithContext cs' MP MCP ->
        head MP = (m',p') -> (* This checks that MP is actually real *)
        WithContext cs (notfinished (m,p) MP) (notfinished (m,cs,p) MCP).

    (* Similarly, with WithObs we relate an MCPTrace into the MPOTrace
       corresponding to its steps annotated with their observations. We feed
       each step's observation forward, to line up with the machine state that follows that step.
       We will need this later. *)
    Inductive WithObs (o:Observation) : MCPTrace -> MPOTrace -> Prop :=
    | WOFinished : forall m c p,
        WithObs o (finished (m,c,p)) (finished (m,p,o))
    | WONotfinished : forall m c p m' c' o' p' MP MPO,
        WithObs o' MP MPO ->
        mpstep (m,p) = Some ((m',p'),o) ->
        head MP = (m',c',p') ->
        WithObs o (notfinished (m,c,p) MP) (notfinished (m,p,o) MPO).

    (* ObsOfMCP starts the observation with Tau, reflecting that initially
       there is no observation until a step occurs. *)
    Definition ObsOfMCP := WithObs Tau.

    (* ContextSegment relates two MCPTraces given a condition f on machine and context states,
       where the second is a longest subtrace of the first such that f holds on all elements
       except the final. So, it will always have at least two elements, and its head will have been
       preceded by one on which f does not hold, while the last (if any) also does not have f hold.
       
       We will use this machinery to clip out sections of a trace that we want to check
       against a property, with the final state reflecting the state after some relevant execution.
     *)
    Inductive ContextSegment (f : MachineState -> ContextState -> Prop) : MCPTrace -> MCPTrace -> Prop :=
    | CSCurrent : forall MCP MCP' m cs p,
        head MCP = (m,cs,p) ->
        f m cs ->
        PrefixUpTo (fun '(m,cs,p) => ~ f m cs) MCP MCP' ->
        ContextSegment f (notfinished (m,cs,p) MCP) (notfinished (m,cs,p) MCP')
    | CSNot : forall MCP MCPpre MCPsuff MCP' m cs p,
        head MCP = (m,cs,p) ->
        ~ f m cs ->
        SplitInclusive (fun '(m,cs,p) => f m cs) MCP MCPpre MCPsuff ->
        ContextSegment f MCPsuff MCP' ->
        ContextSegment f MCP MCP'
    | CSSkip : forall MCP MCPpre MCPsuff MCP' m cs p,
        head MCP = (m,cs,p) ->
        f m cs ->
        SplitInclusive (fun '(m,cs,p) => f m cs) MCP MCPpre MCPsuff ->
        ContextSegment f MCPsuff MCP' ->
        ContextSegment f MCP MCP'
    .
  End WITH_STATE.

  Arguments WithContext {_}  _ _ _ _.
  Arguments ContextSegment {_} _ _ _.
  Arguments ObsOfMCP {_}.
  Arguments MCPState {_}.
  Arguments MCPTrace {_}.
  Arguments cstate {_}.
  
  (* Now let's rephrase our ad-hoc code safety property into one that is slightly
     less ad hoc, that now protects components any time they're marked as code, even
     if they changed later in the execution. Note that we instantiate the context state
     with our domain map, and its initial state and update function. 

     Here we use context segment to always give us a pair of adjacent states in the form
     of (notfinished (m,cs,p) (finished (m',cs',p'))). *)
  Definition CodeSafetyWithContext : Prop :=
    forall minit MCP m cs p m' cs' p' k,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = code ->
      m k = m' k.

  (* We have enough to start working on a more complex property: coroutine safety.
     Coroutine safety is intuitively the property that when a coroutine is active -
     determined by the stack pointer pointing somewhere in its stack - no other
     stack should be read or written. Let's start with something close to our
     code safety - coroutine integrity, just the property that we can't write
     to a stack while it's inactive.

     This looks very much like code safety, except that only care about protecting
     k when the k is in a stack that is not active. We call this a hyper-eager
     property, because just as with code safety, we always look at pairs of states. *)
  Definition CoroutineIntegrityHyperEager : Prop :=
    forall minit MCP m cs p m' cs' p' k sid os sd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = stack sid (Inactive os sd) ->
      os <> shared ->
      activeStack sm m <> sid ->
      m k = m' k.

  (* We haven't yet seen any confidentiality properties - properties guaranteeing the
     secrecy of components, in this case components in an inactive stack. Let's stick
     to the hyper-eager style for now. We'll introduce a few new concepts.

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

  Definition unshared (sd : StackDomain) : Prop :=
    match sd with
    | Active shared _ => False
    | Active _ _ => True
    | Inactive shared _ => False
    | Inactive _ _ => True
    end.

  Definition CoroutineConfidentialityHyperEager : Prop :=
    forall minit MCP m cs p o m' cs' p' sid sd n n' o',
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP  (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      activeStack sm m <> sid ->
      variantOf (fun k => cs k = stack sid sd /\ unshared sd) m n ->
      step n = (n',o) ->
      mpstep (m,p) = Some (m',p',o') ->
      (o = o' /\ sameDifference m m' n n').

  (* Now, within a given coroutine, it is largely unnecessary to vary at each step,
     and in a testing setting this may be costlier than varying at the beginning of the
     coroutine and checking that the variation preserved behavior all the way to when
     the coroutine yielded away.

     We therefore want a confidentiality property for coroutines that treats as secret
     the specific values in hidden locations at the time that control passes to a coroutine that
     shouldn't read them. This means varying the first state of a subtrace from when we leave a
     coroutine to when we return to it, and checking that for the entire subtrace, behavior
     is unchanged as above. Behavior is more complicated now, as the original trace might have
     three different qualities:

     1. it might end with a final state where the coroutine that can read k is active
     2. it might end prematurely, due to a fail stop
     3. it might diverge and run forever without reaching the appropriate coroutine

     In case 1, the variant trace should reach a *convergent* state, one that is also in that coroutine.
        The traces should be observationally equivalent and the convergent states should be same-different.
     In case 2, the variant trace will not end, but its observations should be prefixed by the original.
     In case 3, the variant trace should be observationally equivalent to the original.

     We need to introduce some predicates on states to talk about these traces having similar
     behavior. Stuck represents a trace that fail-stops before ever returning to the coroutine
     whose data is being protected. *)

  Definition Stuck (MPO : MPOTrace) : Prop :=
    exists m p o,
      Last MPO (m,p,o) ->
      mpstep (m,p) = None.

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
  (* We will use this definition of trace confidentiality in many contexts!
     Note that this is a property a single trace with respect to a single component
     k. We must ask: is it a problem to consider components separately in this scenario?
     Could a program whose execution depends on multiple components (k1, k2, ...) pass
     the confidentiality property for k1, for k2, and so on considered separately?

     Indeed it can. Suppose we have an instruction that directly reads two addresses and
     outputs their logical or. Clearly, the value printed by the instruction depends on both
     addresses. But if k1 and k2 each have value 1 at the start of a trace MCP, and this instruction
     accesses them, then for that trace all k1-variations behave the same, and all k2-variations
     behave the same, even though a hypothetical variation where (k1 = k2 = 0) would behave differently.

     But, we are going to quantify over all such traces that are possible in our system,
     so I will argue that considering one component at a time is good enough. *)
(* APT: Hmm. *)
  
  (* Coroutine confidentiality: for each component k belonging to stack sid,
     for each trace segment where sid is inactive, trace confidentiality of k holds
     with convergence meaning that sid becomes active. Unless of course k has been
     shared, in which case all bets are off. *)
  Definition CoroutineConfidentialityEager : Prop :=
    forall minit MCP MCP' sid sd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      let K := fun k => cstate (head MCP') k = stack sid sd /\ unshared sd in
      let Converge := fun n => activeStack sm n = sid in
      TraceConfidentiality MCP' K Converge.

  (* Let's give a similar treatment to integrity. Suppose we wanted to test integrity
     of a system with coroutines. We don't actually need to check at every step that integrity
     is maintained; if we're considering a component that belongs to a coroutine, we need only
     check that from when that coroutine is inactive to when it becomes active again, the
     component remains unchanged. So we can examine a trace for integrity of a component: *)
  Definition TraceIntegrity (MCP:MCPTrace) (K:Component -> Prop) : Prop :=
    forall m (cs:DomainMap) p m' cs' p' k,
      K k ->
      head MCP = (m,cs,p) ->
      Last MCP (m',cs',p') ->
      m k = m' k.
  (* Note that if MCP is infinite, it fulfills trace integrity trivially. *)

  (* Now we have our eager, but not hyper-eager, coroutine integrity.
     It is similar to the confidentiality property. *)
  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP MCP' sid sd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      let K := fun k => cstate (head MCP') k = stack sid sd /\ unshared sd in
      TraceIntegrity MCP' K.
  
  (* Notice how coroutines have the nice property that a stack is always
     either active or inactive, and we can always read and write the active
     stack and never an inactive one. Confidentiality and integrity won't
     always line up, even in more interesting coroutine models, and certainly
     not in our subroutine model. We introduce a concept of contours to
     keep track of these separate security concepts.

     A contour is just a map from a component to a pair of levels:
     - LC/HC: low and high confidentiality
     - LI/HI: low and high integrity
     (See machine.v for the definition of contour)

     So far we've seen code being (LC,HI) and stacks being (LC,LI) vs. (HC,HI).
     What kinds of components are (HC,LI)? Most notably ones that are uninitialized.
     We'll get into that more, but first lets use contours with the ideas we've just
     seen to create a very general property. *)

  Definition SafetyProperty (ContourOf : MachineState -> DomainMap -> Contour)
             (SegmentProp : MachineState -> DomainMap -> Prop) :=
    forall minit MCP MCP' m dm p C,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment SegmentProp MCP MCP' ->
      head MCP' = (m,dm,p) ->
      ContourOf m dm = C ->
      let ProtectedK := (fun k => integrityOf (C k) = HI) in
      TraceIntegrity MCP ProtectedK /\
      let VariedK := (fun k => confidentialityOf (C k) = HC) in
      let Converged := (fun m => ~ SegmentProp m dm) in
      TraceConfidentiality MCP VariedK Converged.

  (* See how we can reimplement our code and coroutine properties as instances of this safety property. *)
  Definition CodeContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | code => (LC,HI)
      | _ => (LC,LI)
      end.
  
  Definition CodeSafety : Prop :=
    SafetyProperty CodeContour (fun _ _ => False).

  Definition CoroutineContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | stack sid sd =>
        if sidEq (Some sid) (Some (activeStack sm m))
        then (LC,LI)
        else (HC,HI)
      | _ => (LC, LI)
      end.

  Definition CoroutineSafety : Prop :=
    forall sid,
      SafetyProperty CoroutineContour (fun m _ => activeStack sm m <> sid).

  (* SNA: revisit this *)
  (* If a component is in the active frame, it is to be treated
     as uninitialized: (HC,LI).
     If it is inactive and local, it is instead (HC,HI).
     But if it is inactive and passed or shared, it is (LC,LI).
     Inactive and shared is treated as if it's in the active frame
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

  Definition extends (sd' sd : StackDomain) :=
    sd' = sd \/ exists os, sd' = Inactive os sd.

  (* So the final stack safety policy instantiates safety, quantifying over base configurations
     for each stack and taking segments that extend those stack. In other words, we consider each
     function activation and include all nested calls within its trace. *)
  Definition StackSafety : Prop :=
    forall s sd,
      SafetyProperty SubroutineContour (fun m dm => exists k sd', dm k = stack s sd' /\ extends sd' sd).

  (* SNA: as APT noted above, there is a version of stack safety in which the residual
     data of a call should not be accessible after it returns. In this variant we would need
     confidentiality to apply to subtraces where sd' = sd, i.e. separate subtraces withing
     an activations. *)

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
  
End WITH_MAPS.

(* APT: What is the status of the WBCF properites? *)
