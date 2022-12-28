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
Notation " 'check' A , B ; C" := (if A then C else Show.trace B (checker false))
                                   (at level 200, A at level 100, B at level 200, C at level 200).
Notation " 'get' X <- A , B ; C" := (match A with
                                     | Some X => C
                                     | None => Show.trace B (checker false)
                                     end)
                                      (at level 60, X at level 60, A at level 60, B at level 200, C at level 200).

Notation " 'iff' B , X <- A ; C" := (X <- (if B then A else ret X) ;; C)
                                      (at level 60, X at level 60, A at level 60, B at level 200, C at level 200).

(* NOTE Not concentrating on eager properties at the moment, focusing changes on
   lazy properties (not including lockstep integrity). *)
Module TestPropsRISCVSimple : TestProps RISCVLazyOrig RISCVDef.
  Import RISCVLazyOrig.
  Import TagPolicyLazyOrig.
  Import RISCVDef.
  Import PM.
  
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

  Definition get_ops (m : MachineState) (cm : CodeMap_Impl) : Operations :=
    match (CodeMap_fromImpl cm) (word.unsigned (getPc (fst m))) with
    | Some ops => ops
    | None => [] (* shouldn't happen, but delegating error handling now *)
    end.

  Definition step (m : MachineState) (cm : CodeMap_Impl)
    : MachineState * list Operation * Observation :=
    let ops := get_ops m cm in
    let '(m', _ (* always empty! *), obs) := step m in
    (m', ops, obs).

  Definition uncoercion4 (op : Operation) : RISCVMachine.RISCV.Operation :=
    match op with
    | Call f reg_args stk_args => RISCVMachine.RISCV.Call f reg_args stk_args
    | Tailcall f reg_args stk_args => RISCVMachine.RISCV.Call f reg_args stk_args
    | Return => RISCVMachine.RISCV.Return
    | Alloc off sz => RISCVMachine.RISCV.Alloc off sz
    | Dealloc off sz => RISCVMachine.RISCV.Dealloc off sz
    end.

  Definition mpstep (m : MPState) (cm : CodeMap_Impl)
    : MPState * list RISCVMachine.RISCV.Operation * RISCVMachine.RISCV.Observation :=
    let ops := get_ops m cm in
    let '(m', _ (* always empty! *), obs) := mpstep m in
    (m', map uncoercion4 ops, obs).

  Derive Show for Sec.

  Definition cstep (m : State) (cm : CodeMap_Impl)
    : MachineState * Ctx * list Operation * Observation :=
    let ops := get_ops (fst m) cm in
    let '(m', _ (* always empty! *), obs) := cstep m in
    let m'_fix :=
      (fst m', fold_left (GenRISCVLazyOrig.PM.op (fst m)) ops (snd m')) in
    (m'_fix, ops, obs).

  (* END HACK *)

  Definition defFuel := 42%nat.

  Derive Show for Element.

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
          let '(m', ctx', _ops, obs) := cstep (m, ctx) cm in
          (* Take a step of the shadow state *)
          let '(n',_,obs') := step n cm in
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
    List.filter (fun k => negb (sameDifferenceP ms ms' ns ns' k)) (getElements ms').

  Definition BinCondition : Type := nat * (State -> State -> list Element).
  Definition Deferred : Type := nat * State * BinCondition.

  (*Definition Witness : Type := Element * nat * nat.*)

  Derive Show for Element.

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
    Show.trace ("Generating variant for: " ++ show secret ++ nl) (
    ns <- GenRISCVLazyOrig.genVariantByList secret ms;;
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
          | Some (e',_) => event_eqb e e'
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
          get ops <- (CodeMap_fromImpl cm) (word.unsigned (getPc (fst (fst m)))), ("Bad-PC: " ++ show (proj (fst m) PC) ++ nl);
          (* Take a step in the primary and the shadow states *)
          let '(m', _ops, obs) := cstep m cm in
          let '(n', _, obs') := step n cm in
          let d := depthOf (snd m) in
          let d' := depthOf (snd m') in
          let tr' := obs::tr in
          (* Check the observations *)
          check (obs_eqb obs obs'), "External Violation: " ++ show obs ++ "/" ++ show obs' ++ " at " ++ show (proj (fst m) PC) ++ nl;
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
               n'' <- GenRISCVLazyOrig.genVariantByList witnesses n';;
               Show.trace ("New shadow variants: " ++ show (map (fun k => (k, proj n'' k)) witnesses) ++ nl)
               (aux fuel' m' n'' stk'' tr')
          else aux fuel' m' n' stk tr'
  end in
  aux fuel m n [] [].
  
  Fixpoint prop_lazyStackConfidentiality
    fuel (i : LayoutInfo) m (cm : CodeMap_Impl) ctx : Checker.Checker :=
    confidentiality_tester cm i fuel (m, ctx) m.

  (* cex03 will ordinarily pass if n'' is computed based on n', but testing the
     same example repeatedly will cause it to fail

     cex02 will also pass with this change

     in this case genMach still finds counterexamples, which tend to be more
     complex

     after policy and property adjustments:

     cex02 fails due to reuse at the same level between executions

     the innocuous cex03 passes

     genMach still finds longer counterexamples, such as cex04, where the
     variant gets stuck (and therefore out of sync) due to step_until_done
     selecting (most of) the code memory as witness and mutating it into
     non-instructions *)

  Definition cex05 : G (MachineState * CodeMap_Impl) :=
    GenRISCVLazyOrig.ex_gen
      [(   0, Addi 2 2 12,  [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (   4, Sw 2 9 (-4),  [Tinstr],        Some [] );
       (   8, Jal 1 264,    [Tinstr; Tcall], Some [(Call 4%nat [] [])] );
       (  12, Jal 1 208,    [Tinstr; Tcall], Some [(Call 3%nat [] [])] );
       (  16, Jal 1 368,    [Tinstr; Tcall], Some [(Call 7%nat [] [])] );
       (  20, Jal 1 344,    [Tinstr; Tcall], Some [(Call 6%nat [] [])] );
       (  24, Jal 1 304,    [Tinstr; Tcall], Some [(Call 5%nat [] [])] );
       (  28, Jal 1 124,    [Tinstr; Tcall], Some [(Call 2%nat [] [])] );
       (  32, Jal 1 52,     [Tinstr; Tcall], Some [(Call 1%nat [] [])] );
       (  36, Jal 1 312,    [Tinstr; Tcall], Some [(Call 5%nat [] [])] ); (* ! *)
       (* f1 *)
       (  84, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       (  88, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (  92, Lw 9 2 (-8),    [Tinstr],        Some [] );
       (  96, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 100, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 104, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f2 *)
       ( 152, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 156, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 160, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 164, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 168, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f3 *)
       ( 220, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 224, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 228, Sw 2 10 (-8),   [Tinstr],        Some [] ); (* ??? *)
       ( 232, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 236, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 240, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f4 *)
       ( 272, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 276, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 280, Sw 2 0 (-4),    [Tinstr],        Some [] );
       ( 284, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 288, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 292, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f5 *)
       ( 328, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 332, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 336, Lw 8 2 (-8),    [Tinstr],        Some [] ); (* ??? *)
       ( 340, Addi 9 10 464,  [Tinstr],        Some [] );
       ( 344, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 348, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 352, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f6 *)
       ( 364, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 368, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 372, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 376, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 380, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f7 *)
       ( 384, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 388, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 392, Sw 2 0 (-20),   [Tinstr],        Some [] );
       ( 396, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 400, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 404, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] )]
      [(  8, 16, [] );
       (  9,  4, [] );
       ( 10, 40, [] )].

  (* The generated example fails (frequently, but not always) because calls are
     not annotated with registers carrying information across calls, i.e.,
     acting as parameters (missing information added here). This is to be
     expected, given that irrelevant registers will be mutated and different
     runs will result in different traces. *)
  Definition cex06 : G (MachineState * CodeMap_Impl) :=
    GenRISCVLazyOrig.ex_gen
      [(   0, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (   4, Jal 1 128,      [Tinstr; Tcall], Some [(Call 2%nat [10 (* added *)] [])] );
       (   8, Jal 1 68,       [Tinstr; Tcall], Some [(Call 1%nat [] [])] );
       (  12, Jal 1 272,      [Tinstr; Tcall], Some [(Call 4%nat [10 (* added *)] [])] );
       (  16, Jal 1 220,      [Tinstr; Tcall], Some [(Call 3%nat [10 (* added *)] [])] );
       (* f1 *)
       (  76, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       (  80, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (  84, Lw 8 2 (-4),    [Tinstr],        Some [] );
       (  88, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       (  92, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       (  96, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f2 *)
       ( 132, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 136, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 140, Add 9 1 10,     [Tinstr],        Some [] );
       ( 144, Sw 2 10 (-4),   [Tinstr],        Some [] );
       ( 148, Lw 10 2 (-4),   [Tinstr],        Some [] );
       ( 152, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 156, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 160, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f3 *)
       ( 236, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 240, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 244, Lw 10 2 (-8),   [Tinstr],        Some [] ); (* ??? *)
       (* ( XXX, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *) *)
       (* ( XXX, Lw 1 2 0,       [Tinstr; Tr2],   Some [] ); *)
       (* ( XXX, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] ); *)
       (* f4 *)
       ( 284, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 288, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 292, Lw 10 2 (-4),   [Tinstr],        Some [] );
       ( 296, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 300, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 304, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] )]
      [(  8, 24, [] );
       (  9, 28, [] );
       ( 10, 40, [] )].

  Definition prop_lazyConfidentiality :=
    forAll GenRISCVLazyOrig.cex04 (fun '(m,cm) =>
                      (prop_lazyStackConfidentiality defFuel defLayoutInfo m cm initCtx)).

End TestPropsRISCVSimple.

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
