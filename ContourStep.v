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
   components with it. For instance, the stack frame for a caller belongs to the active frame for that
   caller as well as the sealed portion of the stack for its callee, and additionally belongs to the
   domain of that stack as a whole (in a multi-stack system). *)
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
     at [APT:"and"?] it will be active after the return, so it is active in two contexts.
     If B calls another function C without sharing a2, it should be inactive and
     local in that context.

     Now suppose that B allocates an array at a3 and calls a callee C, giving C a pointer to
     a3 as the argument, so that C can read and write a3. We have:
                                          sp
     -----------------------------------------------
     | A's frame | v | B's frame  | arr | a3 | Empty
     -----------------------------------------------
          a1      a2                a3

     Now what are the statuses of a1, a2, and a3? First, a1 is in a doubly inactive frame;
     it will take two returns before it's active again. It is also local. a2 is in an inactive frame,
     and in that frame it's local; but after a return it will still be inactive but now passed, and
     after a further return it will remain [APT: "once again"?] be active. C will be able to access it. [APT:???]
     Finally a3 is
     in an inactive frame but shared, which is distinct from being passed because it is uninitialized.

(* APT: Passing address of a3 seems like a bit of a red herring. A simpler example would just be if
     A allocates space for a call-by-reference argument that is to be filled in by B (which knows
     where to find it at a fixed offset from the sp).
*)

(* APT: This example also touches on an issue we need to addres: how fine-grained can a property be in controlling access to
     the caller's frame from the callee?  In a capability-based enforecment mechanism, it is natural to arrange that access to
     a stack-allocated variable is limited to holders of a pointer to that variable.  (The lastest Aarhus paper has
     an example.) And we can emulate capabilities using tag-based policies. But I don't see how we can be that precise 
     in a _property_ based on purely static annotations,  since any pointer tracking will necessarily be approximate and 
     will need to be more permissive.
*)

     If we were to give domains unique names, we would identify stack domains by distinct
     activations of each function (perhaps using a counter). But we don't need them to be
     unique, just to capture the appropriate status of each component in the current context
     and contexts that will be returned to.
   *)


  Inductive FrameStatus :=
  | active
  | inactive
  .
  
  (* APT: In addition to examples discussed above, need to give a simple description of what these three mean. *)
  Inductive ObjectStatus :=
  | passed
  | shared
  | local
  .
 
  (* From the perspective of a single function activation, we can treat the layout
     of memory as a partial function from addresses to their statuses. Partial because
     not all addresses are in each stack. *)
  (* APT: move this later? *)
  Definition StackLayout := Addr -> option (FrameStatus * ObjectStatus).

  (* So a domain, which an address might belong to at any given time, is itself a stack
     of such associations. (We will convert this into a layout later.) *)
  Definition StackDomain := list (FrameStatus * ObjectStatus).


  (* We have a well-formedness condition on stack domains, representing monotonicity -
     given an address in a stack, if it active during the current call, then it
     must have been active for the caller as well. *)
  (* APT: Where is this used? *)
  (* APT: Note that in latest Aarhus paper, they deliberately _don't_ want caller to be able to read
     callee's frame after return; that is, confidentiality is more or less symmetric.  Can we model
     that variant? *)
  Inductive StackDomainWF : StackDomain -> Prop :=
  | SDWFnil : StackDomainWF []
  | SDWFactive : forall os sd,
      Forall (fun '(fs,_) => fs = active) sd ->
      StackDomainWF ((active,os)::sd)
  | SDWFinactive : forall os sd,
      StackDomainWF sd ->
      StackDomainWF ((inactive,os)::sd).

  (* APT: But then why not just the following (is this what you had before?)  *)
  Inductive StackDomain' :=
  | Inactive (os:ObjectStatus) (sd:StackDomain)
  | Active (oss:list ObjectStatus)
  .

  (* Finally, the top-level domain type can make a component part of a stack (in which case
     it also needs to know which stack id it belongs to). It can also be code, in the heap, or
     a register. Later we can expand the definition of the heap to extend the model. *)
  Inductive TopD :=
  | stack : StackID -> StackDomain -> TopD
(*APT: Suggest more uniform notation:
  | stack (sid:StackId) (sd:StackDemain)
*)
  | code
  | heap
  | registers
  .

  Definition DomainMap := Component -> TopD.

  Definition LayoutOfDomainMap (dm:DomainMap) : StackLayout :=
    fun a =>
      match dm (Mem a) with
      | stack _ sd => hd_error sd
      | _ => None
      end.
  
End DOMAIN_MODEL.

Section WITH_MAPS.
  (* Now we describe how components are assigned to domains with an initial
     domain map and a update function, given our initial program maps *)

  Variable cdm : CodeMap'.
  Variable sm : StackMap.
  Variable pOf : MachineState -> PolicyState.
  
  Definition initD : DomainMap :=
    fun k =>
      match k with
      | Mem a =>
        if isCode' cdm a
        then code
        else match findStack sm a with
             | Some sid => stack sid [(active,local)]
             | None => heap
             end
      | _ => registers
      end.

(* APT: Does findStack cover the entire potential size of the stack? *)

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
  
  Definition updateD (m:MachineState) (dm:DomainMap) :=
    match AnnotationOf cdm (m (Reg PC)) with
    | Some call => (* A call adjusts the domain map by sealing the caller's frame (wrapping it in "sealed") *)
(* APT: sealed?? *)
                   (* as well as by wrapping the remaining stack in a new instance of "active" *)
      fun k =>
        match k, dm k with
        | Mem a, stack sid sd =>
          if sidEq (Some sid) (Some (activeStack sm m))
          then if wlt a (m (Reg SP))
               then match LayoutOfDomainMap dm a with
                    | Some (_,os)  => stack sid ((inactive,os)::sd)
                    | _ => stack sid [(inactive,local)]  (* APT can this happen?? *)
                    end
               else stack sid ((active,local)::sd)
          else stack sid sd
        | _,_ => dm k
        end
    | Some ret => (* A return unwraps the outermost domain of all components in the initial stack *)
      fun k =>
        match dm k with  (* APT: why do we need two cases? *)
        | stack sid ((inactive,_)::fd) =>
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then
            stack sid fd
          else dm k
        | stack sid ((active,_)::fd) => 
          if sidEq (Some sid) (findStack sm (m (Reg SP))) then 
            stack sid fd
          else dm k
        | _ => dm k
        end

    (* Much needs to be said about sharing. In Machine.v, the sharing annotation contains a register r
       and a function "range" from words to a list (set) of addresses paired with booleans describing whether
       the address is initialized. The addresses that we share are those in the set generated by range
       applied to the contents of r.

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
APT: This is cute, but it still seems pretty ad-hoc, and in this example it requires the value of SP being somehow magically available.
     If we wanted to describe a dynamic array based at an arbitrary register -- then we would need r1,r2 ... 
     Seems better to pass the entire state, or at least the entire register set.
     *)
    | Some (share r f) => (* A share applies only to an object in the active frame, and sets it to shared *)
      fun k =>
        match k with
        | Mem a =>  
          (* APT: This is super awkward. How about changing result of share/range to have type (Addr -> bool option) *)
          if find (fun '(a',b) => weq a' a && b) (f (m (Reg r))) then
            match dm k with
            | stack sid ((active,local)::fd) => stack sid ((active,passed)::fd)
            | _ => dm k   (* APT: can this happen? *)
            end
          else if find (fun '(a',b) => weq a' a && negb b) (f (m (Reg r))) then
                 match dm k with
                 | stack sid ((active,local)::fd) => stack sid ((active,shared)::fd)
                 | _ => dm k
                 end
               else dm k
        | _ => dm k
        end
    | _ => dm
    end.

(* APT: I think we should explore enriching the set of annotations to include, for example, initializing writes
        that would change a location from HC to LC. *)
  
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
    forall minit MCP m cs p m' cs' p' k sid fd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = stack sid fd ->
      activeStack sm m <> sid ->
      m k = m' k.

  (* We haven't yet seen any confidentiality properties - properties guaranteeing the
     secrecy of components, in this case components in an inactive stack. Let's stick
     to the hyper-eager style for now. We'll introduce a few new concepts.

     Firstly: confidentiality is expressed in terms of "variant" states. A k-variant
     state of m is a state that agrees with m at every component other than k. It may also
     agree at k. The intuition is that if the step from a state does the same thing as the
     step from its k-variant, we can't tell from that step what k was, so k is secret.
     We characterize "does the same thing" as producing the same output and changing
     state in the same way. *)
  Definition variantOf (k : Component) (m n : MachineState) :=
    forall k', k <> k' -> m k' = n k'.

(* APT: Is this "changing the state in the same way"? Needs an explanation. *)
  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (m k <> m' k \/ n k <> n' k) ->
      m' k = n' k.

  Definition CoroutineConfidentialityHyperEager : Prop :=
    forall minit MCP m cs p o m' cs' p' k sid fd n n' o',
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (fun _ _ => False) MCP  (notfinished (m,cs,p) (finished (m',cs',p'))) ->
      cs k = stack sid fd ->
      activeStack sm m <> sid ->
      variantOf k m n ->
      step n = (n',o) ->
      mpstep (m,p) = Some (m',p',o') ->
      (o = o' /\ sameDifference m m' n n').

  (* Now there are strange things that happen with a hyper-eager property.
     Consider a program where a coroutine writes to a location in another stack, then
     reads the same location; this would be a violation of hyper-eager confidentiality,
     but in principle nothing secret has been revealed (only erased, violating integrity.)
APT: Couldn't we model this as a change in contour/domain when the write occurs? 
     I don't think the leap in the next sentence is fully justified.

APT: A possibly better reason for moving to subtraces is testing efficiency: 
     (a) HyperEager property would need to be checked until the end of execution.
     (b) there is no need to vary after each step and (I guess?) it is costlier than just varying once.

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

  Definition TraceConfidentiality (MCP:MCPTrace)  (k:Component) (Converge:MachineState -> Prop) : Prop :=
    forall m (cs:DomainMap) p n MO NO,
      head MCP = (m,cs,p) ->
      ObsOfMCP MCP MO -> (* We will mostly operate on the observation-annotated trace MO *)
      variantOf k m n ->
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
     for each trace segment where sid is inactive, trace confidentiality holds
     with convergence meaning that sid becomes active. *)
  Definition CoroutineConfidentialityEager : Prop :=
    forall minit MCP MCP' k sid fd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      initD k = stack sid fd ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      TraceConfidentiality MCP' k (fun n => activeStack sm n = sid).

  (* Let's give a similar treatment to integrity. Suppose we wanted to test integrity
     of a system with coroutines. We don't actually need to check at every step that integrity
     is maintained; if we're considering a component that belongs to a coroutine, we need only
     check that from when that coroutine is inactive to when it becomes active again, the
     component remains unchanged. So we can examine a trace for integrity of a component: *)
  Definition TraceIntegrity (MCP:MCPTrace) (k:Component) : Prop :=
    forall m (cs:DomainMap) p m' cs' p',
      head MCP = (m,cs,p) ->
      Last MCP (m',cs',p') ->
      m k = m' k.
  (* Note that if MCP is infinite, it fulfills trace integrity trivially. *)

  (* Now we have our eager, but not hyper-eager, coroutine integrity.
     It is similar to the confidentiality property. *)
  Definition CoroutineIntegrityEager : Prop :=
    forall minit MCP MCP' k sid fd,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      initD k = stack sid fd ->
      ContextSegment (fun m _ => activeStack sm m <> sid) MCP MCP' ->
      TraceIntegrity MCP' k.

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

  Definition SafetyProperty (C : MachineState -> DomainMap -> Contour)
             (SegmentProp : Component -> MachineState -> DomainMap -> Prop) :=
    forall minit MCP MCP' k m c p,
      WithContext updateD initD (MPTraceOf (minit, pOf minit)) MCP ->
      ContextSegment (SegmentProp k) MCP MCP' ->
      head MCP' = (m,c,p) ->
      (integrityOf ((C m c) k) = HI ->
       TraceIntegrity MCP k) /\
      (confidentialityOf ((C m c) k) = HC ->
       TraceConfidentiality MCP k (fun m => ~ SegmentProp k m c)).

  (* See how we can reimplement our code and coroutine properties as instances of this safety property. *)
  Definition CodeContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | code => (LC,HI)
      | _ => (LC,LI)
      end.
  
  Definition CodeSafety : Prop :=
    SafetyProperty CodeContour (fun _ _ _ => False).

  Definition CoroutineContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match dm k with
      | stack sid fd =>
        if sidEq (Some sid) (Some (activeStack sm m))
        then (LC,LI)
        else (HC,HI)
      | _ => (LC, LI)
      end.

  Definition CoroutineSafety : Prop :=
    forall sid,
      SafetyProperty CoroutineContour (fun _ m _ => activeStack sm m <> sid).

  (* If a component is in the active frame, it is to be treated
     as uninitialized: (HC,LI).
     If it is inactive and local, it is instead (HC,HI).
     But if it is inactive and passed, the passing overrides the sealing  (APT: "sealing"? )
     and it is (LC,LI).
     Inactive and shared is treated as if it's in the active frame
     At some point it may be useful to distinguish a read-only sharing that is (LC,HI).*)
  Definition SubroutineContour (m:MachineState) (dm:DomainMap) : Contour :=
    fun k =>
      match k with
      | Mem a =>
        match LayoutOfDomainMap dm a with
        | Some (active, _) => (HC,LI)
        | Some (inactive, local) => (HC,HI)
        | Some (inactive, shared) => (LC,LI)
        | Some (inactive, passed) => (HC,LI)
        | _ => (LC,LI)
        end
      | _ => (LC,LI)
      end.

  Definition extends (sd' sd : StackDomain) :=
    exists e, sd' = e ++ sd.

  (* So the final stack safety policy instantiates safety, quantifying over base configurations
     for each stack and taking segments that extend those stack. In other words, we consider each
     function activation and include all nested calls within its trace. *)
  Definition StackSafety : Prop :=
    forall s sd,
      SafetyProperty SubroutineContour (fun k m dm => exists sd', dm k = stack s sd' /\ extends sd' sd).

  (****** Lazy Properties ******)
  
  (* Some enforcement methods do not actually completely enforce our safety properties,
     but instead guarantee that illegal reads and writes are caught after the fact, before
     they are able to affect the observable behavior of the program. In particular, lazy
     policies allow writes to a high-integrity location, but "taint" it so that a fail-stop
     will occur on read. Effectively, it becomes high-confidentiality, permanently, once
     the write occurs. This is represented by establishing that if a component has changed at
     the final state, then any k-variant of that final state must have the same or prefixed
     behavior (where prefix indicates that the system fail-stopped later.) *)
  
  Definition TraceIntegrityLazy (MCP:MCPTrace) (k:Component) : Prop :=
    forall m (dm dm':DomainMap) p m' p',
      head MCP = (m,dm,p) ->
      Last MCP (m',dm',p') ->
      m k <> m' k ->  
      forall m'', variantOf k m' m'' ->
                  ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf  m'').


  (* We might instead reset k to what it was initially. *)
  Definition RollbackInt (k:Component) (Mstart Mend : MachineState) : MachineState :=
    fun k0 => if keqb k k0 then Mstart k0 else Mend k0.

  (* This produces an even weaker property, in which it is permissible to
     alter k and even to later access it, as long as the remaining execution 
     is not observably changed. Such scenarios are easy to construct relative 
     to a well-understood program, such as multiplying a value that is always
     treated as a boolean by a nonzero constant, but are difficult to generalize. *)
  Definition TraceIntegrityLazier (MCP:MCPTrace) (k:Component) : Prop :=
    forall m (dm dm':DomainMap) p m' p',
      head MCP = (m,dm,p) ->
      Last MCP (m',dm',p') ->
      ObsOfMP (MPRunOf (m',p')) <=_O ObsOfM (RunOf (RollbackInt k m m')).

  (* If we substitute one of these properties for TraceIntegrity in the general safety
     property, we have lazy versions of each of our safety properties. *)
  
End WITH_MAPS.

(* APT: What is the status of the WBCF properites? *)
