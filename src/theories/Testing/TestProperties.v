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
Require Import riscv.Utility.MonadNotations.
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

(* To debug, use [Show.trace] with the printers defined in [PrintRISCVLazyOrig] *)

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
  Definition calcTraceDiff cm (m m' : MachineState) (* (p p' : PolicyState) *) (c c' : Ctx) (i : LayoutInfo) (o : Observation) : unit -> string :=
    let compsToTrace :=
        List.filter (fun k => 
                       (orb (negb (Value_equivb (proj m k) (proj m' k)))
                            false))
                            (* (interestingComponent c c' k))) *) (* FIXME *)
                                  (*(andb (TagSet_eqb (pproj p k) (pproj p k))*)
                    (getElements m') in
    (fun tt => 
       ("Observation: " ++ show o ++ nl ++
                        "from: " ++ nl ++
                        concatStr (List.map (fun k => PrintRISCVLazyOrig.printComponent k m cm c i ++ nl) compsToTrace) ++
                        "to: " ++ nl ++
                        concatStr (List.map (fun k => PrintRISCVLazyOrig.printComponent k m' cm c' i ++ nl) compsToTrace) ++ nl)%string).

  (* Depends on deleted code from TestSubroutineSimple *)
  Definition integrityComponent (c : Ctx) (k : Element) :=
    match fst c k with
    | sealed => true
    | _ => false
    end.

  Fixpoint walk (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : Ctx) (m' : MachineState) (c' : Ctx) (traceOut : list (unit -> string))
           (cont : unit -> Checker) : Checker :=
    match ks with
    | [] => cont tt
    | k :: ks' =>
      if integrityComponent c k then
        if Value_equivb (proj m k) (proj m' k)
        then walk ks' cm m c m' c' traceOut cont
        else (*whenFail ("Initial Machine:" ++ nl ++
                                          concatStr (List.rev (List.map (fun f => f tt) traceOut)) ++
                                          "Integrity failure at component: " ++ show k ++ nl ++
                                          "Component values: " ++ show (proj m k) ++ " vs " ++ show (proj m' k) ++ nl ++
                                          "Final state: " ++ nl ++
                                          printMachine m p cm c)%string*) checker false
      else walk ks' cm m c m' c' traceOut cont
    end.
  
  Definition prop_SimpleStackIntegrityStep fuel i m cm ctx
    : Checker.Checker :=
    let fix aux fuel m ctx traceOut : Checker.Checker :=
        match fuel with
        | O => collect "Out-of-Fuel" true
        | S fuel' => 
          let '(m', c', t, o) := cstep (m,ctx) in (* No failstop *)
          let traceDiff :=
            calcTraceDiff cm m m' ctx c' i o in
          walk (getElements m') cm m ctx m' c'
            (traceDiff :: traceOut)
            (fun tt => aux fuel' m' c' (traceDiff :: traceOut))
        end in
    aux fuel m ctx ([fun tt => (*printMachine m p cm ctx*) ""]).

  Definition prop_integrity :=
    let sm := defStackMap defLayoutInfo in
    forAll GenRISCVLazyOrig.genMach (fun '(m,cm) =>
                      (prop_SimpleStackIntegrityStep defFuel defLayoutInfo m cm initCtx)).

  (* - endP could depend on the policy state now
     - cstep can't failstop, doesn't use cm *)
  Fixpoint prop_lockstepConfidentiality
         (fuel :nat)
         (m n : MachineState)
         (cm : CodeMap_Impl) (ctx : Ctx)
         (endP : State -> bool)
    : Checker.Checker :=
    (* trace (printMachines m n p cm ctx ++ nl)   *)
    match fuel with
    | O => checker true
    | S fuel' => 
      match endP (m,ctx), endP (n,ctx) with
      | true, true => (* collect "Both done" *) checker true
      | true, _    => (* collect "Main done" *) checker false
      | _   , true => (* collect "Vary done" *) checker false
      | _, _ =>
        let '(m', c1, t1, o1) := cstep (m, ctx) in
        let '(n', c2, t2, o2) := cstep (n, ctx) in
        if List.forallb (sameDifferenceP m m' n n') (getElements m')
        then prop_lockstepConfidentiality fuel' m' n' cm c1 endP
        else checker false
      end
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

  Fixpoint prop_stackConfidentiality
             fuel (i : LayoutInfo) (m : MachineState) (cm : CodeMap_Impl) ctx
    : Checker.Checker :=
    match fuel with
    | O => collect ("Out of fuel") true
    | S fuel' =>
      match (CodeMap_fromImpl cm) (word.unsigned (getPc (fst m))) with
      | Some call =>
        let '(m', c', t, o) := cstep (m, ctx) in
        let depth := depthOf c' in
        let endP  := fun '(_,c) =>
                       (Nat.ltb (depthOf c) depth) in
        let secret := List.filter (fun k => confidentialityComponent c' k) (getElements m') in
        bindGen (GenRISCVLazyOrig.genVariantByList secret m')
          (fun n =>
             (conjoin
                ([prop_lockstepConfidentiality defFuel m' n cm c' endP] ++
                   [prop_stackConfidentiality fuel' i m' cm c'])))
      | _ =>
        let '(m', c', t, o) := cstep (m, ctx) in
        prop_stackConfidentiality fuel' i m' cm c'
      end
    end.

  Definition prop_confidentiality :=
    let sm := defStackMap defLayoutInfo in
    forAll GenRISCVLazyOrig.genMach (fun '(m,cm) =>
                      (prop_stackConfidentiality defFuel defLayoutInfo m cm initCtx)).

  Fixpoint prop_laziestLockstepIntegrity
           fuel m n (cm : CodeMap_Impl (* unused *)) ctx
    : Checker.Checker :=
    match fuel with
    | O => checker true
    | S fuel' =>
      let '(m', c1, t1, o1) := cstep (m ,ctx) in
      let '(n', c2, t2, o2) := cstep (n ,ctx) in
      if obs_eqb o1 o2 then
        prop_laziestLockstepIntegrity fuel' m' n' cm c1
      else (*whenFail ("Primary: " ++ show o1 ++ " | Variant: " ++ show o2 ++ nl ++
             "Final state: " ++ nl ++ printMachine m p cm ctx)%string*) checker false
    end.

  Definition calcTraceDiff' cm (m m' : MachineState) (c c' : Ctx) (i : LayoutInfo) : unit -> string :=
    let compsToTrace :=
        List.filter (fun k => 
                       (orb (negb (Value_equivb (proj m k) (proj m' k)))
                            (* (interestingComponent c c' k))) *)
                            false)) (* FIXME *)
                                  (*(andb (TagSet_eqb (pproj p k) (pproj p k))*)
                    (getElements m') in
    (fun tt => 
       ("From: " ++ nl ++
                 concatStr (List.map (fun k => PrintRISCVLazyOrig.printComponent k m cm c i ++ nl) compsToTrace) ++ 
                 "to: " ++ nl ++
                 concatStr (List.map (fun k => PrintRISCVLazyOrig.printComponent k m' cm c' i ++ nl) compsToTrace) ++ nl)%string).
  
  Fixpoint walk' (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : Ctx) (m' : MachineState) (c' : Ctx) (changed : list Element) : Checker :=
    match ks with
    | [] =>
      match changed with
      | [] => checker true
      | _ =>
        (*trace (show (List.length changed) ++ nl)*)
        (bindGen (GenRISCVLazyOrig.genVariantByList changed m')
                 (fun n =>
                    prop_laziestLockstepIntegrity defFuel m' n cm c'))
      end
    | k :: ks' =>
      if integrityComponent c k then
        if Value_equivb (proj m k) (proj m' k)
        then walk' ks' cm m c m' c' changed
        else walk' ks' cm m c m' c' (k::changed)
      else walk' ks' cm m c m' c' changed
    end.

  Definition prop_checkAtReturn fuel mcall cm ctxcall
    : Checker.Checker :=
    let fix aux fuel m ctx : Checker.Checker :=
        match fuel with
        | O => collect "Out-of-Fuel" true
        | S fuel' => 
          let '(m', ctx', t, o) := cstep (m, ctx) in
          if (depthOf ctx' <? depthOf ctxcall)%nat then
            walk' (getElements m') cm mcall ctxcall m' ctx' []
          else aux fuel' m' ctx'
        end in
    aux fuel mcall ctxcall.

  Fixpoint prop_laziestStackIntegrity
           fuel (i : LayoutInfo) (m : MachineState) (cm : CodeMap_Impl) ctx : Checker.Checker :=
    match fuel with
    | O => checker true
    | S fuel' =>
      match (CodeMap_fromImpl cm) (word.unsigned (getPc (fst m))) with
      | Some call =>
        let '(m', c', t, o) := cstep (m, ctx) in
        let depth := depthOf c' in
        (*trace ("callee depth: " ++ show depth ++ "   size of sealed: " ++
          (show (List.length (List.filter sealed (getComponents m'))) ++ nl))*)
        (conjoin
           ([prop_checkAtReturn defFuel m' cm c'] ++
            [prop_laziestStackIntegrity fuel' i m' cm c']))
      | _ =>
          let '(m', c', t, o) := cstep (m, ctx) in
          prop_laziestStackIntegrity fuel' i m' cm c'
      end
    end.

  Definition prop_laziestIntegrity :=
    forAll GenRISCVLazyOrig.genMach (fun '(m,cm) =>
                      (prop_laziestStackIntegrity defFuel defLayoutInfo m cm initCtx)).

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

  (* A generic tester for integrity-like properties (no variant generation at
     the moment) *)
  Definition step_tester
    (cm : CodeMap_Impl) (li : LayoutInfo)
    (fuel : nat)
    (m : MachineState) (ctx : Ctx)
    (conds : list (nat * (MachineState -> Ctx -> bool)))
    (gen : MachineState -> Ctx -> CodeMap_Impl ->
           (MachineState -> Ctx -> bool))
    : Checker :=
    let fix aux fuel m ctx conds :=
      (* See if we have enough fuel to take a step, otherwise exit *)
      match fuel with
      | O => collect "Out-of-Fuel" true
      | S fuel' =>
          (* Try to take a step, exit if we are stuck *)
          let '(m', ctx', _ops, _obs) := cstep (m, ctx) in
          (* If we could step, verify that the new state satisfies all
             active tests, otherwise raise an error *)
          let check_cond '(depth, test) :=
            negb ((Nat.eqb depth (depthOf ctx')) && (test m' ctx')) in
          match seq.all check_cond conds with
          | false => collect "Bad-checks" false
          | true =>
              (* Check the code map at the current PC (this should never
                 fail) *)
              match (CodeMap_fromImpl cm) (word.unsigned (getPc (fst m))) with
              | None => collect "Bad-PC" false (* TODO Check *)
              | Some ops =>
                  (* Recurse on the new state, where if the instruction
                     corresponds to a call (assuming a well-formed code map
                     without nonsensical lists of operations) a new test is
                     added to the list *)
                  let conds' :=
                    if ops_call ops
                    then let cond := gen m' ctx' cm in (* Before/after call? *)
                         (depthOf ctx, cond) :: conds
                    else conds in
                  aux fuel' m' ctx' conds'
              end
          end
      end
    in
    aux fuel m ctx conds.

  (* A boolean version of [walk'], where the base case simply checks the
     accumulator and makes the overall walk succeed iff it is empty (i.e., no
     elements of interest were changed). *)
  Fixpoint walk'' (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : Ctx) (m' : MachineState) (c' : Ctx) (changed : list Element) : bool :=
    match ks with
    | [] =>
      match changed with
      | [] => true
      | _ =>
          (* This does not make sense in this context *)
        (* (*trace (show (List.length changed) ++ nl)*) *)
        (* (bindGen (genVariantByList changed m') *)
        (*          (fun n => *)
        (*             prop_laziestLockstepIntegrity defFuel m' n p' cm c')) *)
          false
      end
    | k :: ks' =>
      if integrityComponent c k then
        if Value_equivb (proj m k) (proj m' k)
        then walk'' ks' cm m c m' c' changed
        else walk'' ks' cm m c m' c' (k::changed)
      else walk'' ks' cm m c m' c' changed
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
    : MachineState -> Ctx -> bool :=
    fun m' ctx' =>
      walk'' (getElements m') cm m ctx m' ctx' [].

  (* The top-level properties are now simple instantiations *)
  Fixpoint prop_laziestStackIntegrity'
    fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    step_tester cm i fuel m ctx [] cond_laziestStackIntegrity.

  Definition prop_laziestIntegrity' :=
    forAll GenRISCVLazyOrig.genMach (fun '(m,cm) =>
                      (prop_laziestStackIntegrity' defFuel defLayoutInfo m cm initCtx)).

  (* From above, only operating on MPCState *)
  Definition cond_confidentiality (m m' n n' : State) : bool :=
    let '(ms, _) := m in
    let '(ms', _) := m' in
    let '(ns, _) := n in
    let '(ns', _) := n' in
    List.forallb (sameDifferenceP ms ms' ns ns') (getElements ms').

  (* TODO Monadic notation for added readability *)
  Definition confidentiality_tester
    (cm : CodeMap_Impl) (li : LayoutInfo)
    (fuel : nat)
    (mcur : State) (stk : list (State * nat * State * State))
    : Checker :=
    let fix aux fuel mcur stk :=
      (* See if we have enough fuel to take a step, otherwise exit *)
      match fuel with
      | O => collect "Out-of-Fuel" true
      | S fuel' =>
          (* Try to take a step, exit if we are stuck (no more) *)
          let '(m', _ops, _obs) := cstep mcur in
          (* If the main run steps, try to take the same step in all current
             variants (this should be the same step, with the same
             operations, but we do not check this at the moment) *)
          let step_var '(ncur, depth, mcall, ncall) :=
            let '(n', ops, _obs) := cstep ncur in
            (* No observations for now *)
            (ncur, n', depth, mcall, ncall, ops)
          in
          let stk' := seq.map step_var stk in
          (* (Variants don't get out of sync by getting stuck now) *)
          (* No general checks being performed at the moment, only lazy
             confidentiality; continue checking the current operation.
             The temporary stack is decorated with the observations and
             original pre-step states, which are used to check to find
             return points as they occur, perform checks and pop
             variants from the stack. *)
          let check_var '(ncur, n', depth, mcall, ncall, ops) :=
            match ops_ret ops, (depthOf (snd n') =? depth)%nat with
            | true, true =>
                (* ... *)
                match cond_confidentiality mcur m' ncur n' with
                | false => None (* Error *)
                | true =>
                    Some [] (* Pop variant *)
                end
            | _, _ => (* TODO Check missing/nonsensical cases *)
                Some [(n', depth, mcall, ncall)] (* Update variant *)
            end
          in
          let stk'' := seq.map check_var stk' in
          let stk''' := seq.pmap id stk'' in
          let stk'''' := seq.flatten stk''' in
          (* We need to distinguish three possible outcomes:
             - Return at matching depth, successful check, variant pop
             - Return at matching depth, failed check, error
             - Other step, no changes
             Here using options of 0-or-1-element lists
             Other checks are possible, e.g., only once check should
             take place at most (currently not done)
             The check that is in place is *)
          match (seq.size stk'' =? seq.size stk''')%nat with
          | false =>
              whenFail
                "Confidentiality violation!"
                (collect "Confidentiality-Violation" false)
          | true =>
              match (CodeMap_fromImpl cm) (word.unsigned (getPc (fst (fst mcur)))) with
              | None => collect "Bad-PC" true (* TODO Check *)
              | Some ops =>
                  match ops_call ops with
                  | false =>
                      aux fuel' m' stk''''
                  | true =>
                      (* Before or after call? *)
                      let '(ms', cs') := m' in
                      (* From above, somewhat simplified *)
                      let secret := List.filter (fun k => confidentialityComponent cs' k) (getElements ms') in
                      bindGen (GenRISCVLazyOrig.genVariantByList secret ms')
                        (fun n =>
                           let npc := (n, cs') in (**)
                           let frame := (npc, depthOf cs', mcur, npc (**)) in
                           conjoin [aux fuel' m' (frame :: stk'''')]
                        )
                  end
              end
          end
      end
    in
    aux fuel mcur stk.

  Fixpoint prop_lazyStackConfidentiality
    fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    confidentiality_tester cm i fuel (m, ctx) [].

  Definition prop_lazyConfidentiality :=
    forAll GenRISCVLazyOrig.genMach (fun '(m,cm) =>
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

Extract Constant defNumTests => "5000".

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
