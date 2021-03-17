Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.

From StackSafety Require Import Trace Machine ObsTrace.


Module SubroutineSimple (M: MachineSpec).
  Import M.
  Module O := ObsTrace(M).
  Import O.

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
(* APT: Do we need to distinguish Unsealed from Outside? *)


  (* All components belong to domain, and a domain map tells us which. *)
  Definition DomainMap := Component -> StackDomain.
  
End DOMAIN_MODEL.

Section WITH_MAPS.

  (* The Code and Stack maps tell us about the initial layout of memory, as determined
     by the compiler. They will help us build our initial DomainMap and identify
     calls and returns in the code, in the form of annotations. *)

  (* sm is a simplified stack map that merely identifies whether an address is in the stack *)
  Variable sm : Addr -> bool.
  Variable pOf : MachineState -> PolicyState. (* Policy initialization function. *)

  (* The stack pointer is by far the most typical, but technically other mechanisms could be
     used to seal addresses. We assume that which addresses are being sealed is deducible from
     the machine state (e.g., by comparing them to the stack pointer)
     and attempting to re-seal already sealed addresses is a no-op. *)
  Definition SealingConvention : Type := MachineState -> Addr -> bool.
  Definition sc : SealingConvention :=
    fun m a => wlt a (proj m (Reg SP)).

  (* We will use the machinery defined at the end of Machine.v to extend traces of the
     machine with context that will inform our properties. In this case the context is a
     pair of a DomainMap and a natural number representing the current depth of the stack. *)

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

  (* Our update function checks an "annotation" on the code being executed.
     Annotations are defined in Machine.v, and the ones that matter here are call and return.
     The annotations are carried by a Code Map, which also tells us which addresses are code. *)
  Variable cdm : CodeMap.
  
  Definition updateC (m:MachineState) (prev:context) : context :=
    let '(dm, d) := prev in
    match AnnotationOf cdm (proj m PC) with
    | Some call => (* On a call, we check what the sealing convention wants to seal.
                      If a component is Sealed, it can't be sealed again under the new depth.
                      Everything else retains its old status, presumably Unsealed. In the standard,
                      stack pointer-based sealing convention, sc seals everything below the stack
                      pointer, but previously sealed frames retain their old owners. *)
      let dm' := fun k =>
                    match k, dm k with
                    | _, Outside => Outside
                    | Mem a, Unsealed =>
                      if sc m a
                      then Sealed d
                      else Unsealed
                    | _, _ => Outside
                    end in
      (dm', d+1)
    | Some ret => (* On a return, we unseal everything sealed by the highest sealed depth. That will
                     always be one less than the current depth. Everything else remains. *)
      let dm' := fun k =>
                    match dm k with
                    | Sealed d' =>
                      if d-1 =? d'
                      then Unsealed
                      else Sealed d'
                    | _ => dm k
                    end in
      (dm', d-1)
    | _ => (dm, d)
    end.

  (* Here are some helper relations that take an initial mp state, initial context,
     and a predicate P on states and contexts, and finds a segment MCP where P holds on all contexts
     except the last one, if any. *)
  Definition FindSegmentMP (P : MachineState -> context -> Prop) (mp : MPState) c MCP :=
    exists MCP',
      WithContextMP updateC c (MPTraceOf mp) MCP' /\
      ContextSegment P MCP' MCP.
  
  (* Now it's quite simple to define an "ultra eager" integrity property:
     if we run from any initial state, updating the context as above, then
     at any particular state where a component k is in an Sealed domain,
     k has the same value in the following state (if any.) We term this property
     ultra eager because it "checks" at each step that components that are inaccessible
     don't change, the most frequently it is possible to check. *)
  Definition SimpleStackIntegrityUE : Prop :=
    forall minit k d m c p m' p' o MCP,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (m,c,p) MCP ->
      mpstep (m,p) = Some (m',p',o) ->
      fst c k = Sealed d ->
      proj m k = proj m' k.

  (* In addition to integrity, we have a confidentiality property. Consider in our
     example when B called C and then D. Suppose that B has some secret data, say a capability on some
     system critical resource, that A, C and D should not access. Clearly, D should not read
     B's sealed memory to find it. But it is possible that it could be left behind in the
     memory B deallocated, so that to D, it is not sealed. So we could use "sealedness" to determine
     when something should be confidential, but it is not sufficient.

     Confidentiality requires that we protect the entire stack from being read until it's initialized.
     This is not amenable to an ultra eager property under this model. Instead we will introduce
     the notion of confidentiality using a separate property that only protects Sealed memory, whether or
     not it has been initialized. We'll call it Sealed Confidentiality. This will show us the tools
     we need to implement all sorts of confidentiality properties. The full ultra eager property would
     require us to explicitly track all writes, to determine when a location has been initialized.
     That is beyond our scope at present.

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

  (* Once again, we take adjacent pairs of states in the trace from an arbitrary
     start state and check that a property holds between them. In this case, that
     in any K-variant of the first state where K is the set of components that are
     Sealed in that state, the step has the same observable behavior and makes
     the same changes to state. *)
  Definition SealedConfidentialityUE : Prop :=
    forall minit m c p m' p' d n o n' p'' o' MCP,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (m,c,p) MCP ->
      variantOf (fun k => fst c k = Sealed d) m n ->
      mpstep (m,p) = Some (m',p',o) ->
      mpstep (n,p) = Some (n',p'',o') ->
      sameDifference m m' n n' /\ p' = p'' /\ o = o'.

  (* Some things to note: we have hypotheses that both (m,p) and (n,p) step. So we do not consider
     variant states in which (n,p) has a policy violation. We also require that the policy states
     match after the step. This might not be necessary.

     Again, we are not protecting uninitialized memory - it will turn out that when we leave behind
     the Ultra Eager properties, that protection will come naturally. *)

  (* For integrity, ultra eager properties are significantly stronger than we actually
     need. In fact, we want to consider lazy policies that allow illegal writes at times
     in the name of efficiency. So we should consider what our actual goal is here - what
     use are these properties? Here is an example of how we might think of a program logic
     call rule that lets us guarantee that from a call point, the next matching return
     steps to the same point in the program, and all sealed memory is unchanged. *)
  Definition CallRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall mp o m' c' p' MCP',
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP -> (* From any state that is a call *)
      AnnotationOf cdm (proj mcall PC) = Some call -> (* As determined by the code annotations *)
      mpstep (mcall,pcall) = Some (mp,o) -> (* That has a successful step, i.e. doesn't immediately fail-stop *)

      (* We can look ahead to the next state whose depth is <= dcall, and take the intervening trace,
         or an infinite trace if there is no such state. *)
      FindSegmentMP (fun m '(dm,d) => d > dcall) mp (updateC mcall (dmcall,dcall)) MCP' ->
      Last MCP' (m',c',p') ->
      (* And that state will maintain the values of all sealed addresses. *)
      forall a,
        sc mcall a = true ->
        proj mcall (Mem a) = proj m' (Mem a).      


  (* We could use this as our ultimate specification, or just to guide our trace
     properties. Note that this rule cares nothing for what happens to the state of
     the Sealed components in the middle of the call, only that whe we return, they are
     the same. Our eager property reflects this; instead of guaranteeing that they never
     change, it guarantees that they are unchanged if and when the function returns. *)
  Definition SimpleStackIntegrityEager : Prop :=
    forall minit MCP d d' k mcp mcp',
      FindSegmentMP  (fun m c => snd c >= d) (minit, pOf minit) initC MCP ->
      mcp = head MCP ->
      fst (cstate mcp) k = Sealed d' ->
      Last MCP mcp' ->
      proj (mstate mcp) k = proj (mstate mcp') k.

  Theorem EagerIntSufficient :
    SimpleStackIntegrityEager ->
    CallRule.
  Proof.
  Admitted.
  
  (* We can make a similar argument about confidentiality, though it may be odd to
     think of a confidentiality call rule. We can at least think of the following as
     the "caller's view" of confidentiality: that the behavior of the callee does not
     depend on any of the stack state at the call.

     Since we aren't modeling any sharing of memory yet, this means that the functions
     communicate only through registers. *)
  Definition ConfRule : Prop :=
    forall minit MCP mcall dmcall dcall pcall m p o n MCP' N MO NO,
      WithContextMP updateC initC (MPTraceOf (minit, pOf minit)) MCP ->
      InTrace (mcall,(dmcall,dcall),pcall) MCP -> (* Once again we consider each successful call *)
      AnnotationOf cdm (proj mcall  PC) = Some call ->
      mpstep (mcall,pcall) = Some (m,p,o) ->

      (* And take any variant state of the first state within it *)
      variantOf (fun k => dmcall k <> Outside) m n ->
      (* If we trace from both states until they each return... *)
      FindSegmentMP (fun _ '(dm,d) => d >= dcall) (m,p) (dmcall,dcall) MCP' ->
      FindSegmentMP (fun _ '(dm,d) => d >= dcall) (n,p) (dmcall,dcall) N ->
      (* They should have the same observable behavior *)
      ObsOfMCP MCP' MO ->
      ObsOfMCP N NO ->
      ObsOfMP MO ~=_O ObsOfMP NO /\
      (* And when they return, the states should have changed in identical ways. *)
      (forall m' dm' p',
          Last MCP' (m',(dm',dcall),p') ->
          exists n' dm'',
            Last N (n',(dm'',dcall),p') /\
            sameDifference mcall m' n n').

  (* The flip side of the caller's rule is the trace property that holds on subtraces
     representing calls. This only needs to be strong enough to support the caller-side
     reasoning, so here is an example of such an eager (but not ultra-eager) property. *)
  Definition SimpleStackConfidentialityEager : Prop :=
    forall minit M MO d m dm p n N NO,
      let P := (fun m c => snd c = d) in
      FindSegmentMP P (minit, pOf minit) initC M ->
      head M = (m,(dm,d),p) ->
      variantOf (fun k => dm k <> Outside) m n ->
      FindSegmentMP P (n,p) (dm,d) N ->
      ObsOfMCP M MO ->
      ObsOfMCP N NO ->
         (* Case 1 *)
      (forall mend dmend pend,
          Last M (mend,dmend,pend) ->
          ~ P mend (dm,d) ->
          exists nend dnend,
            Last N (nend,dnend,pend) /\
            ObsOfMP MO ~=_O ObsOfMP NO /\
            sameDifference m mend n nend)
      /\ (* Case 2 *)
      (Infinite M ->
       ObsOfMP MO ~=_O ObsOfMP NO)
      /\ (* Case 3 *)
      (forall mend dmend pend,
          Last M (mend, dmend, pend) ->
          P mend (dm,d) ->
          ObsOfMP MO <=_O ObsOfMP NO).

  Theorem EagerConfSufficient :
    SimpleStackConfidentialityEager ->
    ConfRule.
  Proof.
  Admitted.

  (* Now the above properties do a few things all at once that it helps to disentangle. They
     quantify over all initial states, then over all segments of a trace at or above a certain
     depth on the stack, ending with the return when the depth is reduced. And they state
     properties of those segments. Lets focus on just capturing what it means for a trace
     to respect the integrity and confidentiality of components, and separate out the finding
     of the traces. The predicate K will indicate the set of components that must be protected. *)

  Definition TraceIntegrityEager (K : Component -> Prop) (MCP:MCPTrace) : Prop :=
    forall k (mcp':@MCPState context),
      K k->
      Last MCP mcp' ->
      proj (mstate (head MCP)) k = proj (mstate mcp') k.

  (* The confidentiality trace property needs to know when the variant trace can be considered to have
     returned, for which it takes a predicate on states and contexts, P. *)
  Definition TraceConfidentialityEager (K : Component -> Prop)
             (P:MachineState -> context -> Prop)
             (MCP:@MCPTrace context) : Prop :=
    forall MCP MO d m dm p n N NO,
      head MCP = (m,(dm,d),p) ->
      variantOf K m n ->
      FindSegmentMP P (n,p) (dm,d) N ->
      ObsOfMCP MCP MO ->
      ObsOfMCP N NO ->
         (* Case 1 *)
      (forall mend dmend pend,
          Last MCP (mend,dmend,pend) ->
          ~ P mend (dm,d) ->
          exists nend dnend,
            Last N (nend,dnend,pend) /\
            ObsOfMP MO ~=_O ObsOfMP NO /\
            sameDifference m mend n nend)
      /\ (* Case 2 *)
      (Infinite MCP ->
       ObsOfMP MO ~=_O ObsOfMP NO)
      /\ (* Case 3 *)
      (forall mend dmend pend,
          Last MCP (mend, dmend, pend) ->
          P mend (dm,d) ->
          ObsOfMP MO <=_O ObsOfMP NO).

  (* Now we can quantify over all initial states and segments starting with calls,
     to create a property of the system that all calls enjoy both confidentiality and
     integrity. *)
  Definition StackSafety :=
    forall minit MCP m dm d p,
      let P := (fun m '(dm, d') => d' >= d) in
      FindSegmentMP P (minit, pOf minit) initC MCP ->
      head MCP = (m,(dm,d),p) ->
      let Ki := (fun k => exists d, dm k = Sealed d) in
      TraceIntegrityEager Ki MCP /\
      let Kc := (fun k => dm k <> Outside) in
      TraceConfidentialityEager Kc P MCP.

  Theorem StackSafetySufficient :
    StackSafety ->
    CallRule /\ ConfRule.
  Proof.
  Admitted.

  (* ***** Control Flow Properties ***** *)

    Definition ControlSeparation : Prop :=
    forall minit m1 p1 m2 p2 o f1 f2 ann1 ann2,
      InTrace (m1,p1) (MPTraceOf (minit, pOf minit)) ->
      mpstep (m1,p1) = Some (m2, p2,o) ->
      cdm (proj m1  PC) = inFun f1 ann1 ->
      cdm (proj m2  PC) = inFun f2 ann2 ->
      f1 <> f2 ->
      AnnotationOf cdm (proj m1 PC) = Some call \/
      AnnotationOf cdm (proj m1 PC) = Some ret.

  Definition ReturnIntegrity : Prop :=
    forall d minit MCP m c p m' c' p',
      let P := fun m c => snd c >= d in
      FindSegmentMP P (minit, pOf minit) initC MCP ->
      head MCP = (m,c,p) ->
      Last MCP (m',c',p') ->
      justRet m m'.

  Variable em:EntryMap.
  
  Definition EntryIntegrity : Prop :=
  forall minit mp1 m2 p2 o,
    InTrace mp1 (MPTraceOf (minit, pOf minit)) ->
    mpstep mp1 = Some (m2,p2,o) ->
    AnnotationOf cdm (proj (ms mp1) PC) = Some call ->
    em (proj m2 PC) = true.

  Definition WellBracketedControlFlow  : Prop :=
    ControlSeparation /\
    ReturnIntegrity /\
    EntryIntegrity.
  
  (* Continue to SubroutineShare.v, where we enhance the model with sharing between calls. *)

End WITH_MAPS.

End SubroutineSimple.

