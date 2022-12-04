From StackSafety Require Import MachineModule PolicyModule TestingModules
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
  
  Definition calcTraceDiff cm (m m' : MachineState) (p p' : PolicyState) (c c' : CtxState) (i : LayoutInfo) (o : Observation) : unit -> string :=
    let compsToTrace :=
        List.filter (fun k => 
                       (orb (negb (Z.eqb (proj m k) (proj m' k)))
                            (interestingComponent c c' k)))
                                  (*(andb (TagSet_eqb (pproj p k) (pproj p k))*)
                    (getElements m') in
    (fun tt => 
       ("Observation: " ++ show o ++ nl ++
                        "from: " ++ nl ++
                        concatStr (List.map (fun k => printComponent k m p cm c i ++ nl) compsToTrace) ++ 
                        "to: " ++ nl ++
                        concatStr (List.map (fun k => printComponent k m' p' cm c' i ++ nl) compsToTrace) ++ nl)%string).

  
  Fixpoint walk (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (p : PolicyState) (c : CtxState) (m' : MachineState) (p' : PolicyState) (c' : CtxState) (traceOut : list (unit -> string))
           (cont : unit -> Checker) : Checker :=
    match ks with
    | [] => cont tt
    | k :: ks' =>
      if integrityComponent c k then
        if Z.eqb (proj m k) (proj m' k)
        then walk ks' cm m p c m' p' c' traceOut cont
        else (*whenFail ("Initial Machine:" ++ nl ++
                                          concatStr (List.rev (List.map (fun f => f tt) traceOut)) ++
                                          "Integrity failure at component: " ++ show k ++ nl ++
                                          "Component values: " ++ show (proj m k) ++ " vs " ++ show (proj m' k) ++ nl ++
                                          "Final state: " ++ nl ++
                                          printMachine m p cm c)%string*) checker false
      else walk ks' cm m p c m' p' c' traceOut cont
    end.
  
  Definition prop_SimpleStackIntegrityStep fuel i m p cm ctx
    : Checker.Checker :=
    let fix aux fuel m p ctx traceOut : Checker.Checker :=
        match fuel with
        | O => collect "Out-of-Fuel" true
        | S fuel' => 
          match mpcstep (m,p,ctx) cm with
          | None => collect ("Failstop", fuel) true
          | Some (m', p', c', t, o) =>
            let traceDiff :=
                calcTraceDiff cm m m' p p' ctx c' i o in
            walk (getElements m') cm m p ctx m' p' c'
                 (traceDiff :: traceOut)
                 (fun tt => aux fuel' m' p' c' (traceDiff :: traceOut))
          end
        end in
    aux fuel m p ctx ([fun tt => (*printMachine m p cm ctx*) ""]).

  Definition prop_integrity :=
    let sm := defStackMap defLayoutInfo in
    forAll genMach (fun '(m,p,cm) =>
                      (prop_SimpleStackIntegrityStep defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).
  
  Fixpoint prop_lockstepConfidentiality
         (fuel :nat)
         (m n : MachineState) (p : PolicyState)
         (cm : CodeMap_Impl) (ctx : CtxState)
         (endP : MPCState -> bool)
    : Checker.Checker :=
    (* trace (printMachines m n p cm ctx ++ nl)   *)
    match fuel with
    | O => checker true
    | S fuel' => 
      match endP (m,p,ctx), endP (n,p,ctx) with
      | true, true => (* collect "Both done" *) checker true
      | true, _    => (* collect "Main done" *) checker false
      | _   , true => (* collect "Vary done" *) checker false
      | _, _ =>
        match mpcstep (m,p,ctx) cm,
              mpcstep (n,p,ctx) cm with
        | Some (m',p1,c1,t1,o1), Some (n', p2,c2, t2, o2) =>
          if List.forallb (sameDifferenceP m m' n n') (getElements m')
          then prop_lockstepConfidentiality fuel' m' n' p1 cm c1 endP
          else checker false
        | _, _ => checker true
        end
      end
    end.

  Fixpoint prop_stackConfidentiality
             fuel (i : LayoutInfo) m p (cm : CodeMap_Impl) ctx 
    : Checker.Checker :=
    match fuel with
    | O => collect ("Out of fuel") true
    | S fuel' =>
      match (CodeMap_fromImpl cm) (word.unsigned (getPc m)) with
      | Some call =>
        match mpcstep (m,p,ctx) cm with
        | Some (m', p', c', t, o) =>
          let depth := depthOf c' in
          let endP  := fun '(_,_,c) =>
                         (Nat.ltb (depthOf c) depth) in
          let secret := List.filter (fun k => confidentialityComponent c' k) (getElements m') in
          bindGen (genVariantByList secret m')
                   (fun n =>
                      (conjoin
                         ([prop_lockstepConfidentiality defFuel m' n p' cm c' endP] ++
                          [prop_stackConfidentiality fuel' i m' p' cm c'])))
        | _ => collect ("Failstop",fuel) true
        end
      | _ =>
        match mpcstep (m,p,ctx) cm with
        | Some (m', p', c', t, o) =>
          prop_stackConfidentiality fuel' i m' p' cm c'
        | _ => collect ("Failstop",fuel) true
        end
      end
    end.

  Definition prop_confidentiality :=
    let sm := defStackMap defLayoutInfo in
    forAll genMach (fun '(m,p,cm) =>
                      (prop_stackConfidentiality defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).


  Fixpoint prop_laziestLockstepIntegrity
           fuel m n p cm ctx
    : Checker.Checker :=
    match fuel with
    | O => checker true
    | S fuel' =>
      match mpcstep (m,p,ctx) cm,
            mpcstep (n,p,ctx) cm with
      | Some (m',p1,c1,t1,o1), Some (n',p2,c2,t2,o2) =>
        if obs_eqb o1 o2 then
          prop_laziestLockstepIntegrity fuel' m' n' p1 cm c1
        else (*whenFail ("Primary: " ++ show o1 ++ " | Variant: " ++ show o2 ++ nl ++
                       "Final state: " ++ nl ++ printMachine m p cm ctx)%string*) checker false

      | _, _ => collect "Failstop after return" true
      end
    end.

  Definition calcTraceDiff' cm (m m' : MachineState) (p p' : PolicyState) (c c' : CtxState) (i : LayoutInfo) : unit -> string :=
    let compsToTrace :=
        List.filter (fun k => 
                       (orb (negb (Z.eqb (proj m k) (proj m' k)))
                            (interestingComponent c c' k)))
                                  (*(andb (TagSet_eqb (pproj p k) (pproj p k))*)
                    (getElements m') in
    (fun tt => 
       ("From: " ++ nl ++
                 concatStr (List.map (fun k => printComponent k m p cm c i ++ nl) compsToTrace) ++ 
                 "to: " ++ nl ++
                 concatStr (List.map (fun k => printComponent k m' p' cm c' i ++ nl) compsToTrace) ++ nl)%string).
  
  Fixpoint walk' (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : CtxState) (m' : MachineState) (p' : PolicyState) (c' : CtxState) (changed : list Element) : Checker :=
    match ks with
    | [] =>
      match changed with
      | [] => checker true
      | _ =>
        (*trace (show (List.length changed) ++ nl)*)
        (bindGen (genVariantByList changed m')
                 (fun n =>
                    prop_laziestLockstepIntegrity defFuel m' n p' cm c'))
      end
    | k :: ks' =>
      if integrityComponent c k then
        if Z.eqb (proj m k) (proj m' k)
        then walk' ks' cm m c m' p' c' changed
        else walk' ks' cm m c m' p' c' (k::changed)
      else walk' ks' cm m c m' p' c' changed
    end.

  Definition prop_checkAtReturn fuel mcall pcall cm ctxcall
    : Checker.Checker :=
    let fix aux fuel m p ctx : Checker.Checker :=
        match fuel with
        | O => collect "Out-of-Fuel" true
        | S fuel' => 
          match mpcstep (m,p,ctx) cm with
          | None => collect "Failstop" true
          | Some (m', p', ctx', t, o) =>
            if (depthOf ctx' <? depthOf ctxcall)%nat then
              walk' (getElements m') cm mcall ctxcall m' p' ctx' []
            else aux fuel' m' p' ctx'
          end
        end in
    aux fuel mcall pcall ctxcall.

  Fixpoint prop_laziestStackIntegrity
           fuel (i : LayoutInfo) m p (cm : CodeMap_Impl) ctx : Checker.Checker :=
    match fuel with
    | O => checker true
    | S fuel' =>
      match (CodeMap_fromImpl cm) (word.unsigned (getPc m)) with
      | Some call =>
        match mpcstep (m,p,ctx) cm  with
        | Some (m', p', c', t, o) =>
          let depth := depthOf c' in
          (*trace ("callee depth: " ++ show depth ++ "   size of sealed: " ++
                                  (show (List.length (List.filter sealed (getComponents m'))) ++ nl))*)
          (conjoin
             ([prop_checkAtReturn defFuel m' p' cm c'] ++
              [prop_laziestStackIntegrity fuel' i m' p' cm c']))
        | _ =>
          checker true
        end
      | _ =>
        match mpcstep (m,p,ctx) cm with
        | Some (m', p', c', t, o) =>
          prop_laziestStackIntegrity fuel' i m' p' cm c'
        | _ => checker true
        end
      end
    end.

  Definition prop_laziestIntegrity :=
    forAll genMach (fun '(m,p,cm) =>
                      (prop_laziestStackIntegrity defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).

  (* A generic tester for integrity-like properties (no variant generation at
     the moment) *)
  Definition step_tester
    (cm : CodeMap_Impl) (li : LayoutInfo)
    (fuel : nat)
    (m : RiscvMachine) (p : PolicyState) (ctx : CtxState)
    (conds : list (nat * (RiscvMachine -> PolicyState -> CtxState -> bool)))
    (gen : RiscvMachine -> PolicyState -> CtxState -> CodeMap_Impl ->
           (RiscvMachine -> PolicyState -> CtxState -> bool))
    : Checker :=
    let fix aux fuel m p ctx conds :=
      (* See if we have enough fuel to take a step, otherwise exit *)
      match fuel with
      | O => collect "Out-of-Fuel" true
      | S fuel' =>
          (* Try to take a step, exit if we are stuck *)
          match mpcstep (m, p, ctx) cm with
          | None => collect "Failstop" true
          | Some (m', p', ctx', _ops, _obs) =>
              (* If we could step, verify that the new state satisfies all
                 active tests, otherwise raise an error *)
              let check_cond '(depth, test) :=
                negb ((Nat.eqb depth (depthOf ctx')) && (test m' p' ctx')) in
              match seq.all check_cond conds with
              | false => collect "Bad-checks" false
              | true =>
                  (* Check the code map at the current PC (this should never
                     fail) *)
                  match (CodeMap_fromImpl cm) (word.unsigned (getPc m)) with
                  | None => collect "Bad-PC" false (* TODO Check *)
                  | Some ops =>
                      (* Recurse on the new state, where if the instruction
                         corresponds to a call (assuming a well-formed code map
                         without nonsensical lists of operations) a new test is
                         added to the list *)
                      let is_call op :=
                        match op with
                        | Call _ _ _ => true
                        | _ => false
                        end in
                      match seq.has is_call ops with
                      | false =>
                          aux fuel' m' p' ctx' conds
                      | true =>
                          (* Before or after call? *)
                          let cond := gen m' p' ctx' cm in
                          aux fuel' m' p' ctx' ((depthOf ctx, cond) :: conds)
                      end
                  end
              end
          end
      end
    in
    aux fuel m p ctx conds.

  (* A boolean version of [walk'], where the base case simply checks the
     accumulator and makes the overall walk succeed iff it is empty (i.e., no
     elements of interest were changed). *)
  Fixpoint walk'' (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : CtxState) (m' : MachineState) (p' : PolicyState) (c' : CtxState) (changed : list Element) : bool :=
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
        if Z.eqb (proj m k) (proj m' k)
        then walk'' ks' cm m c m' p' c' changed
        else walk'' ks' cm m c m' p' c' (k::changed)
      else walk'' ks' cm m c m' p' c' changed
    end.

  (* The condition for the laziest version of stack integrity becomes the core
     of [prop_checkAtReturn], where the condition:
       [if (depthOf ctx' <? depthOf ctxcall)%nat then]
     should be covered by the framework (TODO beware off-by-one errors!). [m],
     [p], [ctx] are the state at the time of instantiation (old [mcall],
     [ctxcall]). The recursive structure of [prop_laziestStackIntegrity] is now
     handled by the tester as well. *)
  Definition cond_laziestStackIntegrity
    (m : RiscvMachine) (p : PolicyState) (ctx : CtxState) (cm : CodeMap_Impl)
    : RiscvMachine -> PolicyState -> CtxState -> bool :=
    fun m' p' ctx' =>
      walk'' (getElements m') cm m ctx m' p' ctx' [].

  (* The top-level properties are now simple instantiations *)
  Fixpoint prop_laziestStackIntegrity'
    fuel (i : LayoutInfo) m p (cm : CodeMap_Impl) ctx : Checker.Checker :=
    step_tester cm i fuel m p ctx [] cond_laziestStackIntegrity.

  Definition prop_laziestIntegrity' :=
    forAll genMach (fun '(m,p,cm) =>
                      (prop_laziestStackIntegrity' defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).

End TestPropsRISCVSimple.

Module TestRISCVEager := TestPropsRISCVSimple RISCVObs TPEager DLObs
                                              TSSRiscvDefault GenRISCVEager
                                              PrintRISCVEager.

Module TestRISCVEagerNLC := TestPropsRISCVSimple RISCVObs TPEagerNLC DLObs
                                              TSSRiscvDefault GenRISCVEagerNLC
                                              PrintRISCVEagerNLC.

Module TestRISCVEagerNSC := TestPropsRISCVSimple RISCVObs TPEagerNSC DLObs
                                              TSSRiscvDefault GenRISCVEagerNSC
                                              PrintRISCVEagerNSC.

Module TestRISCVEagerNI := TestPropsRISCVSimple RISCVObs TPEagerNI DLObs
                                              TSSRiscvDefault GenRISCVEagerNI
                                              PrintRISCVEagerNI.


Module TestRISCVLazyOrig := TestPropsRISCVSimple RISCVObs TPLazyOrig DLObs
                                                   TSSRiscvDefault GenRISCVLazyOrig
                                                   PrintRISCVLazyOrig.

Module TestRISCVLazyNoDepth := TestPropsRISCVSimple RISCVObs TPLazyNoDepth DLObs
                                                    TSSRiscvDefault GenRISCVLazyNoDepth
                                                    PrintRISCVLazyNoDepth.

Module TestRISCVLazyNoCheck := TestPropsRISCVSimple RISCVObs TPLazyNoCheck DLObs
                                                    TSSRiscvDefault GenRISCVLazyNoCheck
                                                    PrintRISCVLazyNoCheck.

Module TestRISCVLazyFixed := TestPropsRISCVSimple RISCVObs TPLazyFixed DLObs
                                                  TSSRiscvDefault GenRISCVLazyFixed
                                                  PrintRISCVLazyFixed.

Extract Constant defNumTests => "5000".
  
Import TestRISCVEager.
Import TestRISCVEagerNLC.
Import TestRISCVEagerNSC.
Import TestRISCVEagerNI.

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

Import TestRISCVLazyOrig.
Import TestRISCVLazyNoDepth.
Import TestRISCVLazyNoCheck.
Import TestRISCVLazyFixed.

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
