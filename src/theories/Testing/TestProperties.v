From StackSafety Require Import MachineModule PolicyModule CtxModule TestingModules
     DefaultLayout Lazy
     PrintRISCVTagSimple GenRISCVTagSimple.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.
Require Import Bool.

Require Import ZArith. Open Scope Z.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Spec.Decode.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.

Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.Minimal.
Require Import riscv.Platform.MinimalLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Z.HexNotation.
Require coqutil.Map.SortedList.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Import ListNotations.

Require Import ExtLib.Structures.Monad. Import MonadNotation. Open Scope monad_scope.

(* To debug, use [Show.trace] with the printers defined in [PrintRISCVLazyOrig] *)

(* Helpful Error-monad-ish notation *)
Notation " 'check' A , B ; C" := (if A then C else collect B false)
                                   (at level 200, A at level 100, B at level 200, C at level 200).
Notation " 'get' X <- A , B ; C" := (match A with
                                    | Some X => C
                                    | None => collect B false
                                    end)
                                     (at level 60, X at level 60, A at level 60, B at level 200, C at level 200).

(* NOTE Not concentrating on eager properties at the moment, focusing changes on
   lazy properties (not including lockstep integrity). *)
Module TestPropsRISCVSimple : TestProps RISCVLazyOrig RISCVDef.
  Import RISCVLazyOrig.
  Import TagPolicyLazyOrig.
  Import RISCVDef.
  Import PM.
  
  Definition defFuel := 42%nat.

  Definition sameDifferenceP (m m' n n' : MachineState) k :=
    if (orb (negb (Z.eqb (projw m k) (projw m' k)))
            (negb (Z.eqb (projw n k) (projw n' k)))) then
      Z.eqb (projw m' k) (projw n' k) 
    else true.

  (* Lifting of Z.eqb, ignoring tags *)
  Definition Value_equivb (v1 v2 : Value) : bool :=
    let '(w1, t1) := v1 in
    let '(w2, t2) := v2 in
    Z.eqb w1 w2.

  (* Depends on deleted code from TestSubroutineSimple *)
  Definition integrityComponent (c : Ctx) (k : Element) :=
    match fst c k with
    | sealed => true
    | _ => false
    end.  

  (* Depends on deleted code from TestSubroutineSimple *)
  Definition confidentialityComponent (c : Ctx) (k : Element) :=
    match fst c k with
    | sealed => true
    | free => true
    | _ => false
    end.

  (* Depends on deleted code from TestSubroutineSimple *)
  Definition depthOf (c : Ctx) := seq.size (snd c).  

  (* Simple operation helpers, no assumptions on well-formedness *)
  Definition op_call (op : Operation) : bool :=
    match op with
    | Call _ _ _ => true
    | _ => false
    end.

  Definition ops_call (ops : Operations) : bool :=
    seq.has op_call ops.

  Definition op_ret (op : Operation) : bool :=
    match op with
    | Return => true
    | _ => false
    end.

  Definition ops_ret (ops : Operations) : bool :=
    seq.has op_ret ops.

  (* a condition consists of a depth at which it should be checked,
     and a function to identify elements that witness a violation.
     If no witnesses are found, the condition holds. *)
  Definition Condition : Type := nat * (State -> list Element).

  (* to test conditions, first check the depth, then collect any witnesses
     and eliminate conditions that have been checked *)
  Fixpoint check_conds (conds:list Condition) (m:State) :=
    match conds with
    | [] => ([],[])
    | (depth,test)::conds' =>
        let (conds'',witnesses) := check_conds conds' m in
        if (Nat.eqb depth (depthOf (snd m)))
        then ((depth,test)::conds,test m ++ witnesses)
        else (conds, witnesses)
    end.

  (* A generic tester for integrity-like properties with laziness *)
  Definition step_tester
    (cm : CodeMap_Impl) (li : LayoutInfo)
    (fuel : nat)
    (m : MachineState) (ctx : Ctx)
    (n : MachineState)
    (conds : list Condition)
    (gen : MachineState -> Ctx -> CodeMap_Impl ->
           (State -> list Element))
    : Checker :=
    let fix aux fuel m ctx n conds :=
      (* See if we have enough fuel to take a step, otherwise exit *)
      match fuel with
      | O => collect "Out-of-Fuel" true
      | S fuel' =>
          let '(m', ctx', _ops, obs) := cstep (m, ctx) in
          (* Take a step of the shadow state *)
          let '(n',_,obs') := step n in
          (* Test that we made the same observations *)
          check (obs_eqb obs obs'), "Lazy Violation";
          (* If we could step, verify that the new state satisfies all
             active tests, and accumulate witnesses to violations *)
          let '(conds', witnesses) := check_conds conds (m', ctx') in
          n'' <- (GenRISCVLazyOrig.genVariantByList witnesses n');;
          (* Check the code map at the current PC (this should never fail) *)
          get ops <- (CodeMap_fromImpl cm) (word.unsigned (getPc (fst m))), "Bad-PC";
          (* Recurse on the new state, where if the instruction
             corresponds to a call (assuming a well-formed code map
             without nonsensical lists of operations) a new test is
             added to the list *)
          let conds'' :=
            if ops_call ops
            then let test := gen m' ctx' cm in (* Before/after call? *)
                 (depthOf ctx, test) :: conds'
            else conds in
          aux fuel' m' ctx' n'' conds'
  end
  in
  aux fuel m ctx n conds.

  (* Walk over the memory and determine which elements of interest were changed). *)
  Fixpoint walk (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : Ctx) (m' : MachineState) : list Element :=
    match ks with
    | [] => []
    | k :: ks' =>
        if integrityComponent c k then
          if Value_equivb (proj m k) (proj m' k)
          then walk ks' cm m c m'
          else k::(walk ks' cm m c m')
        else walk ks' cm m c m'
    end.

  (* The condition for the laziest version of stack integrity becomes the core
     of [prop_checkAtReturn], where the condition:
       [if (depthOf ctx' <? depthOf ctxcall)%nat then]
     should be covered by the framework (TODO beware off-by-one errors!). [m],
     [p], [ctx] are the state at the time of instantiation (old [mcall],
     [ctxcall]). The recursive structure of [prop_laziestStackIntegrity] is now
     handled by the tester as well. *)
  Definition cond_laziestStackIntegrity
    (m : MachineState) (ctx : Ctx) (cm : CodeMap_Impl)
    : State -> list Element :=
    fun '(m',_) =>
      walk (getElements m') cm m ctx m'.

  (* The top-level properties are now simple instantiations *)
  Fixpoint prop_laziestStackIntegrity'
    fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    step_tester cm i fuel m ctx m [] cond_laziestStackIntegrity.

  Definition prop_laziestIntegrity :=
    forAll GenRISCVLazyOrig.genMach (fun '(m,cm) =>
                      (prop_laziestStackIntegrity' defFuel defLayoutInfo m cm initCtx)).

  (* From above, only operating on MPCState *)
  Definition cond_confidentiality (m m' n n' : State) : list Element :=
    let '(ms, _) := m in
    let '(ms', _) := m' in
    let '(ns, _) := n in
    let '(ns', _) := n' in
    List.filter (sameDifferenceP ms ms' ns ns') (getElements ms').

  Definition BinCondition : Type := nat * (State -> State -> list Element).
  Definition Deferred : Type := nat * State * BinCondition.
  
  Fixpoint step_until_done (fuel: nat) (n: State) (cond: BinCondition) (m: State) : list Element * Trace :=
    let (depth, test) := cond in
    if (depthOf (snd n) <=? depth)%nat
    then match fuel with
         | O => ([], Trace.finished Tau)
         | S fuel' =>
             let '(n', _ops, obs) := cstep n in
             let (witnesses, t) := step_until_done fuel' n' cond m in
             (witnesses, Trace.notfinished obs t)
         end
    else
      let witnesses := test m n in
      (witnesses, Trace.finished Tau).

  Fixpoint separate_by_depth (stk:list (nat * State * BinCondition)) (d:nat) :=
    match stk with
    | [] => ([],[])
    | (fuel,m,(depth,test))::stk' =>
        let (ready,not_ready) := separate_by_depth stk' d in
        if (d <=? depth)%nat
        then ((fuel,m,(depth,test))::ready,not_ready)
        else (ready, (fuel,m,(depth,test))::not_ready)
    end.

  (* TODO Did some Monad notation, but the stk' <- ... stuck is nasty *)
  Definition confidentiality_tester
    (cm : CodeMap_Impl) (li : LayoutInfo)
    (fuel : nat)
    (m : State)
    (n : MachineState)
    : Checker :=
    let fix aux fuel m n (stk : list (nat * State * BinCondition)) :=
      (* See if we have enough fuel to take a step, otherwise exit *)
      match fuel with
      | O => collect "Out-of-Fuel" true
      | S fuel' =>
          get ops <- (CodeMap_fromImpl cm) (word.unsigned (getPc (fst (fst m)))), "Bad-PC";
          (* Take a step in the primary and the shadow states *)
          (* FIXME: The current stepping functions always return an empty list
             of operations. We try to work around this by moving up the code map
             check on the PC (which makes sense anyway); we can attempt to use
             this information to update the context of new state [m'] as it
             would have been had the data been available when it should have
             (see [cstep] in [MachineModule]). *)
          let '(m', _ops, obs) := cstep m in
          (* BEGIN HACK *)
          let m' :=
            let '(_ms, _mc) := m' in
            (_ms, fold_left (GenRISCVLazyOrig.PM.op (fst m)) ops _mc) in
          (* END HACK *)
          let '(n', _, obs') := step n in
          (* Check the observations *)
          check (obs_eqb obs obs'), "External Violation";
          (* If we just made a call, push a new variant *)
          stk' <- 
            (if ops_call ops
             then let '(ms', cs') := m' in
                  let secret := List.filter (fun k => confidentialityComponent cs' k) (getElements ms') in
                  ns <- GenRISCVLazyOrig.genVariantByList secret ms';;
                  let nc := (ns,cs') in
                  let test := (fun m'' n'' => cond_confidentiality m' m'' nc n'') in
                  let frame := (fuel', nc, (depthOf cs', test)) in
                  ret (frame::stk)
             else ret stk);;
          if (depthOf (snd m') <? depthOf (snd m))%nat
          then let (ready, stk'') := separate_by_depth stk' (depthOf (snd m')) in
               (* If we just returned to a depth, d, execute all the variants waiting for that depth *)
               let results := map (fun '(fuel,nv,cond) => step_until_done fuel nv cond m') ready in
               (* TODO: Check internal confidentiality *)
            
               (* Collect witnesses *)
               let witnesses := seq.flatten (map fst results) in
               (* Update the shadow state *)
               n'' <- GenRISCVLazyOrig.genVariantByList witnesses n;;
               aux fuel' m' n'' stk''
          else aux fuel' m' n' stk'                   
  end in
  aux fuel m n [].
  
  Fixpoint prop_lazyStackConfidentiality
    fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    confidentiality_tester cm i fuel (m, ctx) m.

  Definition prop_lazyConfidentiality :=
    forAll GenRISCVLazyOrig.cex02 (fun '(m,cm) =>
                      (prop_lazyStackConfidentiality defFuel defLayoutInfo m cm initCtx)).

End TestPropsRISCVSimple.

(* Module TestRISCVEager := TestPropsRISCVSimple RISCVObs TPEager DLObs *)
(*                                               TSSRiscvDefault GenRISCVEager *)
(*                                               PrintRISCVEager. *)

(* Module TestRISCVEagerNLC := TestPropsRISCVSimple RISCVObs TPEagerNLC DLObs *)
(*                                               TSSRiscvDefault GenRISCVEagerNLC *)
(*                                               PrintRISCVEagerNLC. *)

(* Module TestRISCVEagerNSC := TestPropsRISCVSimple RISCVObs TPEagerNSC DLObs *)
(*                                               TSSRiscvDefault GenRISCVEagerNSC *)
(*                                               PrintRISCVEagerNSC. *)

(* Module TestRISCVEagerNI := TestPropsRISCVSimple RISCVObs TPEagerNI DLObs *)
(*                                               TSSRiscvDefault GenRISCVEagerNI *)
(*                                               PrintRISCVEagerNI. *)


(* Module TestRISCVLazyOrig := TestPropsRISCVSimple RISCVObs TPLazyOrig DLObs *)
(*                                                    TSSRiscvDefault GenRISCVLazyOrig *)
(*                                                    PrintRISCVLazyOrig. *)

(* Module TestRISCVLazyNoDepth := TestPropsRISCVSimple RISCVObs TPLazyNoDepth DLObs *)
(*                                                     TSSRiscvDefault GenRISCVLazyNoDepth *)
(*                                                     PrintRISCVLazyNoDepth. *)

(* Module TestRISCVLazyNoCheck := TestPropsRISCVSimple RISCVObs TPLazyNoCheck DLObs *)
(*                                                     TSSRiscvDefault GenRISCVLazyNoCheck *)
(*                                                     PrintRISCVLazyNoCheck. *)

(* Module TestRISCVLazyFixed := TestPropsRISCVSimple RISCVObs TPLazyFixed DLObs *)
(*                                                   TSSRiscvDefault GenRISCVLazyFixed *)
(*                                                   PrintRISCVLazyFixed. *)

Extract Constant defNumTests => "1".

(* Print Assumptions TestPropsRISCVSimple.prop_lazyConfidentiality. *)
Time QuickCheck TestPropsRISCVSimple.prop_lazyConfidentiality.

(* Import TestRISCVEager. *)
(* Import TestRISCVEagerNLC. *)
(* Import TestRISCVEagerNSC. *)
(* Import TestRISCVEagerNI. *)

(* Mutations marked "Fails" are expected to fail, and do! *)
(* Three trials with each mutation for averaging *)
(*Time QuickCheck TestRISCVEagerNLC.prop_confidentiality. (* Fails *)
Time QuickCheck TestRISCVEagerNLC.prop_confidentiality.
Time QuickCheck TestRISCVEagerNLC.prop_confidentiality. *)

(*Time QuickCheck TestRISCVEagerNSC.prop_integrity. (* Fails *)
Time QuickCheck TestRISCVEagerNSC.prop_integrity.
Time QuickCheck TestRISCVEagerNSC.prop_integrity.*)

(*Time QuickCheck TestRISCVEagerNI.prop_integrity. (* Fails *)
Time QuickCheck TestRISCVEagerNI.prop_integrity.
Time QuickCheck TestRISCVEagerNI.prop_integrity.*)

(*Time QuickCheck TestRISCVEager.prop_integrity.
(* Confidentiality hangs sometimes -- better to test it in
   smaller batches (~500) and kill it when needed.
   How we managed to make coq code diverge...
Time QuickCheck TestRISCVEager.prop_confidentiality.*) *)

(* Import TestRISCVLazyOrig. *)
(* Import TestRISCVLazyNoDepth. *)
(* Import TestRISCVLazyNoCheck. *)
(* Import TestRISCVLazyFixed. *)

(*Time QuickCheck TestRISCVLazyOrig.prop_laziestIntegrity. (* Fails *)
Time QuickCheck TestRISCVLazyOrig.prop_laziestIntegrity.
Time QuickCheck TestRISCVLazyOrig.prop_laziestIntegrity.
Time QuickCheck TestRISCVLazyOrig.prop_laziestIntegrity.*)

(*Time QuickCheck TestRISCVLazyNoCheck.prop_confidentiality. (* Fails *)
Time QuickCheck TestRISCVLazyNoCheck.prop_confidentiality.
Time QuickCheck TestRISCVLazyNoCheck.prop_laziestIntegrity. (* Fails *)
Time QuickCheck TestRISCVLazyNoCheck.prop_laziestIntegrity.*)

(*Time QuickCheck TestRISCVLazyNoDepth.prop_confidentiality. (* Fails *)
Time QuickCheck TestRISCVLazyNoDepth.prop_confidentiality.
Time QuickCheck TestRISCVLazyNoCheck.prop_laziestIntegrity. (* Fails *)
Time QuickCheck TestRISCVLazyNoCheck.prop_laziestIntegrity.*)

(*Time QuickCheck TestRISCVLazyFixed.prop_confidentiality.
Time QuickCheck TestRISCVLazyFixed.prop_laziestIntegrity.*)
