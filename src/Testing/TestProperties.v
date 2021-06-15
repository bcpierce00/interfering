From StackSafety Require Import MachineModule PolicyModule TestingModules
     RISCVObs DefaultLayout TestSubroutineSimple PrintRISCVTagSimple GenRISCVTagSimple.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.

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
Import RiscvMachine.

Import TagPolicyLazyFixed.

Module TestPropsRISCVSimple
       (P : Policy RISCV)
       (LI : LayoutInfo RISCV)
       (C : TestCtx RISCV LI)
       (GenImp : Gen RISCV P LI C)
       (PrintImp : Printing RISCV P LI C)
  : TestProps RISCV P LI C.
  Module MPC := TestMPC RISCV P LI C.
  Import MPC.
  Import GenImp.
  Import PrintImp.
  
  Definition defFuel := 42%nat.

  Definition sameDifferenceP (m m' n n' : MachineState) k :=
    if (orb (negb (Z.eqb (proj m k) (proj m' k)))
            (negb (Z.eqb (proj n k) (proj n' k)))) then
      Z.eqb (proj m' k) (proj n' k) 
    else true.
  
  Definition calcTraceDiff cm (m m' : MachineState) (p p' : PolicyState) (c c' : CtxState) (i : LayoutInfo) (o : Observation) : unit -> string :=
    let compsToTrace :=
        List.filter (fun k => 
                       (orb (negb (Z.eqb (proj m k) (proj m' k)))
                            (interestingComponent c c' k)))
                                  (*(andb (TagSet_eqb (pproj p k) (pproj p k))*)
                    (getComponents m') in
    (fun tt => 
       ("Observation: " ++ show o ++ nl ++
                        "from: " ++ nl ++
                        concatStr (List.map (fun k => printComponent k m p cm c i ++ nl) compsToTrace) ++ 
                        "to: " ++ nl ++
                        concatStr (List.map (fun k => printComponent k m' p' cm c' i ++ nl) compsToTrace) ++ nl)%string).

  
  Fixpoint walk (ks : list Component) (cm : CodeMap_Impl) (m : MachineState) (p : PolicyState) (c : CtxState) (m' : MachineState) (p' : PolicyState) (c' : CtxState) (traceOut : list (unit -> string))
           (cont : unit -> Checker) : Checker :=
    match ks with
    | [] => cont tt
    | k :: ks' =>
      if integrityComponent c k then
        if Z.eqb (proj m k) (proj m' k)
        then walk ks' cm m p c m' p' c' traceOut cont
        else whenFail ("Initial Machine:" ++ nl ++
                                          concatStr (List.rev (List.map (fun f => f tt) traceOut)) ++
                                          "Integrity failure at component: " ++ show k ++ nl ++
                                          "Component values: " ++ show (proj m k) ++ " vs " ++ show (proj m' k) ++ nl ++
                                          "Final state: " ++ nl ++
                                          printMachine m p cm c)%string false
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
          | Some (m', p', c', o) =>
            (*          match AnnotationOf (CodeMap_fromImpl cm) (proj m PC) with
                        | Some MachineImpl.ret =>        
                        exception (show ("Trying to ret", List.length (snd ctx), List.length (snd c'), List.map (fun p => p m') (snd ctx), List.map (fun p => p m') (snd c'), List.length (snd c'), List.map (fun p => p m) (snd ctx), List.map (fun p => p m) (snd c')))
                        | _ => *)
            let traceDiff :=
                calcTraceDiff cm m m' p p' ctx c' i o in
            walk (getComponents m') cm m p ctx m' p' c'
                 (traceDiff :: traceOut)
                 (fun tt => aux fuel' m' p' c' (traceDiff :: traceOut))
          end
        end in
    aux fuel m p ctx ([fun tt => printMachine m p cm ctx]).

  Definition prop_integrity :=
    let sm := defStackMap defLayoutInfo in
    forAll genMach (fun '(m,p,cm) =>
                      (prop_SimpleStackIntegrityStep defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).
  
  Fixpoint prop_lockstepConfidentiality
         (fuel :nat)
         (m n : MachineState) (p : PolicyState)
         (cm : CodeMap_Impl) (ctx : CtxState)
         (endP : MPCState -> bool)
    : bool :=
    (* trace (printMachines m n p cm ctx ++ nl)   *)
    (match fuel with
     | O => true
     | S fuel' => 
       match endP (m,p,ctx), endP (n,p,ctx) with
       | true, true => (* collect "Both done" *) true
       | true, _    => (* collect "Main done" *) true
       | _   , true => (* collect "Vary done" *) true
       | _, _ =>
         match mpcstep (m,p,ctx) cm,
               mpcstep (n,p,ctx) cm with
         | Some (m',p1,c1,o1), Some (n', p2,c2, o2) =>
           andb (List.forallb (sameDifferenceP m m' n n') (getComponents m'))
                (prop_lockstepConfidentiality fuel' m' n' p1 cm c1 endP)
         | _, _ => true
         end
       end
     end).

  Definition prop_stackConfidentiality
             fuel (i : LayoutInfo) m p (cm : CodeMap_Impl) ctx 
    : Checker.Checker :=
    match fuel with
    | O => checker true
    | S fuel' =>
      match (CodeMap_fromImpl cm) (word.unsigned (getPc m)) with
      | Some call =>
        match mpcstep (m,p,ctx) cm with
        | Some (m', p', c', o) =>
          let depth := depthOf c' in
          let endP  := fun '(_,_,c) =>
                         (Nat.ltb (depthOf c) depth) in
          forAllShrinkShow (genVariantOf depth c' m')
                           (fun _ => nil)
                           (fun n' => "")
                           (fun n' =>
                              prop_lockstepConfidentiality defFuel m' n' p' cm c' endP)
        | _ => checker true
        end
      | _ => checker true
      end
    end.

  Definition prop_confidentiality :=
    let sm := defStackMap defLayoutInfo in
    forAll genMach (fun '(m,p,cm) =>
                      (prop_stackConfidentiality defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).

    Fixpoint prop_laziestLockstepIntegrity
           fuel m n p ctx cm (endP : MPCState -> bool)
    : bool :=
    match fuel with
    | O => true
    | S fuel' =>
      match endP (m,p,ctx), endP (n,p,ctx) with
      | true, true => (* collect "Both done" *) true
      | true, _    => (* collect "Main done" *) true
      | _   , true => (* collect "Vary done" *) true
      | _, _ =>
        match mpcstep (m,p,ctx) cm,
              mpcstep (n,p,ctx) cm with
        | Some (m',p1,c1,o1), Some (n', p2,c2, o2) =>
          andb (obs_eqb o1 o2)
               (prop_laziestLockstepIntegrity fuel' m' n' p1 c1 cm endP)
        | _, _ => true
        end
      end
    end.
  
  Definition prop_laziestStackIntegrity
           fuel (i : LayoutInfo) m p (cm : CodeMap_Impl) ctx
  : Checker.Checker :=
  match fuel with
  | O => checker true
  | S fuel' =>
    match (CodeMap_fromImpl cm) (word.unsigned (getPc m)) with
    | Some call =>
      match mpcstep (m,p,ctx) cm with
      | Some (m', p', c', o) =>
        let depth := depthOf c' in
        let endP  := fun '(_,_,c) =>
                       (Nat.ltb (depthOf c) depth) in
        forAllShrinkShow (genVariantOf depth c' m')
                         (fun _ => nil)
                         (fun n' => "")
                         (fun n' =>
                            prop_laziestLockstepIntegrity defFuel m' n' p' c' cm endP)
      | _ => checker true
      end
    | _ => checker true
    end
  end.

  Definition prop_laziestIntegrity :=
    let sm := defStackMap defLayoutInfo in
    forAll genMach (fun '(m,p,cm) =>
                      (prop_laziestStackIntegrity defFuel defLayoutInfo m p cm (initCtx defLayoutInfo))).

End TestPropsRISCVSimple.

Module TestRISCVTagSimple := TestPropsRISCVSimple TagPolicyLazyFixed DefaultLayout
                                                  TSS GenRISCVTagSimple
                                                  PrintRISCVTagSimple.

Import TestRISCVTagSimple.

Extract Constant defNumTests => "500".
QuickCheck prop_integrity.
