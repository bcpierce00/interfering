From StackSafety Require Import MachineModule PolicyModule CtxModule TestingModules
     DefaultLayoutLazy DefaultLayoutEager Lazy PrintLazy GenLazy Eager PrintEager GenEager.

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
Notation " 'check' A , B ; C" := (if A then C else Show.trace B (checker false))
                                   (at level 200, A at level 100, B at level 200, C at level 200).
Notation " 'get' X <- A , B ; C" := (match A with
                                     | Some X => C
                                     | None => Show.trace B (checker false)
                                     end)
                                      (at level 60, X at level 60, A at level 60, B at level 200, C at level 200).

Notation " 'iff' B , X <- A ; C" := (X <- (if B then A else ret X) ;; C)
                                      (at level 60, X at level 60, A at level 60, B at level 200, C at level 200).

Definition trace := true.
Notation " S '!' A " := (if trace then Show.trace (S)%string A else A)
                          (at level 60).

Module TestProps (M : Machine) (L : LayoutInfo M) (G : Gen M L) (P : Printing M L): TestProps M L.
  Import M.
  Import L.
  Import G.
  Import P.
  
  (* FIXME: The current stepping functions always return an empty list
     of operations. We try to work around this by moving up the code map
     check on the PC (which makes sense anyway); we can attempt to use
     this information to update the context of new state [m'] as it
     would have been had the data been available when it should have
     (see [cstep] in [MachineModule]). *)

  (* BEGIN HACK *)

  (* Obtain operations from code map, wrap around given (defective) step
     functions and update contexts if applicable. Use only wrappers in the
     properties until a proper fix is implemented. *)
  
  Definition get_ops (m : MachineState) (cm : CodeMap_Impl) : list Operation :=
    match (CodeMap_fromImpl cm) (projw m PC) with
    | Some ops => ops
    | None => [] (* shouldn't happen, but delegating error handling now *)
    end.

  Definition step (m : MachineState) (cm : CodeMap_Impl)
    : MachineState * list Operation * Observation :=
    let ops := get_ops m cm in
    let '(m', _ (* always empty! *), obs) := step m in
    (m', ops, obs).
  
  Derive Show for Sec.

  Definition cstep (m : State) (cm : CodeMap_Impl)
    : MachineState * Ctx * list Operation * Observation :=
    let ops := get_ops (fst m) cm in
    let '(m', _ (* always empty! *), obs) := cstep m in
    let m'_fix :=
      (fst m', fold_left (PM.op (fst m)) ops (snd m')) in
    (m'_fix, ops, obs).

  (* END HACK *)

  Definition defFuel := 100%nat.

(*  Derive Show for Element. *)

  Definition sameDifferenceP (m m' n n' : MachineState) k :=
    if (orb (negb (weq (projw m k) (projw m' k)))
            (negb (weq (projw n k) (projw n' k)))) then
      weq (projw m' k) (projw n' k) 
    else true.

  (* Lifting of Z.eqb, ignoring tags *)
(*  Definition Value_equivb (v1 v2 : Value) : bool :=
    let '(w1, t1) := v1 in
    let '(w2, t2) := v2 in
    Z.eqb w1 w2.*)

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
    | Tailcall _ _ _ => true
    | _ => false
    end.

  Definition ops_call (ops : list Operation) : bool :=
    seq.has op_call ops.

  Definition op_ret (op : Operation) : bool :=
    match op with
    | Return => true
    | _ => false
    end.

  Definition ops_ret (ops : list Operation) : bool :=
    seq.has op_ret ops.

  (* a condition consists of a depth at which it should be checked,
     and a function to identify elements that witness a violation.
     If no witnesses are found, the condition holds. *)
  Definition Condition : Type := nat * (State -> list Element).

  (* to test conditions, first check the depth, then collect any witnesses
     and eliminate conditions that have been checked *)
  Fixpoint check_conds (conds:list Condition) (m:State)
    : list (nat * (State -> list Element)) * list Element :=
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
          let '(m', ctx', _ops, obs) := cstep (m, ctx) cm in
          if weq (projw m' PC) (projw m PC)
          then collect "Failstop" true
          else
          (* Take a step of the shadow state *)
          let '(n',_,obs') := step n cm in
          (* Test that we made the same observations *)
          check (obs_eqb obs obs'), "Lazy Violation";
          (* If we could step, verify that the new state satisfies all
             active tests, and accumulate witnesses to violations *)
          let '(conds', witnesses) := check_conds conds (m', ctx') in
          n'' <- (genVariantByList witnesses n');;
          (* Check the code map at the current PC (this should never fail) *)
          get ops <- (CodeMap_fromImpl cm) (projw m PC), "Bad-PC";
          (* Recurse on the new state, where if the instruction
             corresponds to a call (assuming a well-formed code map
             without nonsensical lists of operations) a new test is
             added to the list *)
          let conds'' :=
            if ops_call ops
            then let test := gen m' ctx' cm in (* Before/after call? *)
                 (depthOf ctx, test) :: conds'
            else conds' in
          aux fuel' m' ctx' n'' conds''
  end
  in
  aux fuel m ctx n conds.

  (* Walk over the memory and determine which elements of interest were changed). *)
  Fixpoint walk (ks : list Element) (cm : CodeMap_Impl) (m : MachineState) (c : Ctx) (m' : MachineState) : list Element :=
    match ks with
    | [] => []
    | k :: ks' =>
        if integrityComponent c k then
          if weq (projw m k) (projw m' k)
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
  Definition cond_Integrity
    (m : MachineState) (ctx : Ctx) (cm : CodeMap_Impl)
    : State -> list Element :=
    fun '(m',_) =>
      walk (getElements m') cm m ctx m'.

  (* The top-level properties are now simple instantiations *)
  Definition test_Integrity
           fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    step_tester cm i fuel m ctx m [] cond_Integrity.

  Definition prop_Integrity :=
    forAll genMach (fun '(m,cm) =>
                      (test_Integrity defFuel defLayoutInfo m cm initCtx)).

  (* From above, only operating on MPCState *)
  Definition cond_confidentiality (m m' n n' : State) : list Element :=
    let '(ms, _) := m in
    let '(ms', _) := m' in
    let '(ns, _) := n in
    let '(ns', _) := n' in
    List.filter (fun k => negb (sameDifferenceP ms ms' ns ns' k)) (getElements ms').

  Definition BinCondition : Type := nat * (State -> State -> list Element).
  Definition Deferred : Type := nat * State * BinCondition.

  (*Definition Witness : Type := Element * nat * nat.*)

  (*Instance show_witness : Show Witness :=
    {| show := (fun '(e,f,i) => "(" ++ show e ++ show f ++ show i ++ ")") |}%string.

  Fixpoint label_witnesses (ks: list Element) (f: nat) : list Witness :=
    match ks with
    | [] => []
    | k::ks' => (k,f,List.length ks')::label_witnesses ks' f
    end.*)
  
  Definition step_until_done (fuel: nat) (n: State) (cond: BinCondition) (m: State) (cm : CodeMap_Impl) : list Element * list Observation :=
    let (depth, test) := cond in
    let fix aux fuel n :=
      match fuel with
      | O => ([], [])
      | S fuel' =>
          let '(n', _ops, obs) := cstep n cm in
          let d' := depthOf (snd n') in
          if (d' <? depth)%nat
          then let witnesses := test m n in
               (witnesses, [obs])
          else let (witnesses, t) := aux fuel' n' in
               (witnesses, obs::t)
      end in
    aux fuel n
  .

  Fixpoint separate_by_depth (stk:list (nat * State * BinCondition)) (d:nat) :=
    match stk with
    | [] => ([],[])
    | (fuel,m,(depth,test))::stk' =>
        let (ready,not_ready) := separate_by_depth stk' d in
        if (d <=? depth)%nat
        then ((fuel,m,(depth,test))::ready,not_ready)
        else (ready, (fuel,m,(depth,test))::not_ready)
    end.

  Definition variant_frame (fuel : nat) (m : State) : G (nat * State * BinCondition) :=
    let '(ms, cs) := m in
    let secret := List.filter (fun k => confidentialityComponent cs k) (getElements ms) in
    (ns <- genVariantByList secret ms;;
    let n := (ns, cs) in
    let test := (fun m' n' => cond_confidentiality m m' n n') in
    ret (fuel, n, (depthOf cs, test))).
  
  Definition mcons {A:Type} (h: G A)  (tl: list A) :=
    head <- h;;
    ret (head :: tl).
  
  Fixpoint trace_sym (base: list Observation) (traces: list (list Observation)) : bool :=
    let fix next tr :=
      match tr with
      | [] => None
      | (Out e)::tr' => Some (e,tr')
      | Tau::tr' => next tr'
      end in
    match base with
    | [] => true
    | Tau::base' => trace_sym base' traces
    | (Out e)::base' =>
        let compare o :=
          match o with
          | None => true
          | Some (e',_) => obs_eqb (Out e) (Out e')
          end in
        let chop := map next traces in
        if forallb compare chop
        then trace_sym base' (seq.pmap (option_map snd) chop)
        else false
    end.
  
  Definition confidentiality_tester
    (cm : CodeMap_Impl) (li : LayoutInfo)
    (fuel : nat)
    (m : State)
    (n : MachineState)
    : Checker :=
    let fix aux fuel m n (stk : list (nat * State * BinCondition)) (tr:list Observation) :=
      (* See if we have enough fuel to take a step, otherwise exit *)
      match fuel with
      | O => collect "Out-of-Fuel" true
      | S fuel' =>
          get ops <- (CodeMap_fromImpl cm) (projw (fst m) PC), ("Bad-PC" (*++ show (proj (fst m) PC)*) ++ nl);
          (* Take a step in the primary and the shadow states *)
          let '(m', _ops, obs) := cstep m cm in
          if weq (projw (fst m') PC) (projw (fst m) PC)
          then collect "Failstop" true
          else
          let '(n', _, obs') := step n cm in
          let d := depthOf (snd m) in
          let d' := depthOf (snd m') in
          let tr' := obs::tr in
          (* Check the observations *)
          check (obs_eqb obs obs'), "External Violation: " ++ show obs ++ "/" ++ show obs' (*++ " at " ++ show (proj (fst m) PC)*) ++ nl;
          (* If we just made a call, push a new variant *)
          iff (ops_call ops), stk <- mcons (variant_frame fuel' m') stk;
          if (d' <? d)%nat
          then let (ready, stk'') := separate_by_depth stk d in (* XXX check depths, see above *)
               (* If we just returned from a depth, d, execute all the variants waiting for that depth *)
               let results := map (fun '(fuel,nv,cond) => step_until_done fuel nv cond m cm) ready in
               (* NEW: Checking state *before* return! *)
               (* Check internal confidentiality *)
               let traces := map snd results in
               check (trace_sym tr traces), "Internal Violation";
               (* Collect witnesses *)
               let witnesses := seq.flatten (map fst results) in
               (* Update the shadow state *)
               n'' <- genVariantByList witnesses n';;
               (*("New shadow variants: " ++ show (map (fun k => (k, proj n'' k)) witnesses) ++ nl) !*)
               (aux fuel' m' n'' stk'' tr')
          else aux fuel' m' n' stk tr'
  end in
  aux fuel m n [] [].
  
  Definition test_Confidentiality
           fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    confidentiality_tester cm i fuel (m, ctx) m.

  Definition prop_Confidentiality :=
    forAll genMach (fun '(m,cm) =>
                      (test_Confidentiality defFuel defLayoutInfo m cm initCtx)).

End TestProps.

Module TestPropsLazy := TestProps RISCVLazyOrig RISCVLazyDef GenRISCVLazyOrig PrintRISCVLazyOrig.
Module TestPropsEager := TestProps RISCVEagerOrig RISCVEagerDef GenRISCVEagerOrig PrintRISCVEagerOrig.

Extract Constant defNumTests => "1000".

Time QuickCheck TestPropsEager.prop_Integrity.
