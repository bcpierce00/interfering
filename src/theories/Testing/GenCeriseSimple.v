From StackSafety Require Import MachineModule PolicyModule TestingModules
     CeriseMachine CeriseLayout TestSubroutineSimple PrintCeriseSimple.

Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.

Require Import ZArith. Open Scope Z.
From stdpp Require Import gmap.
Require Import addr_reg.
Require Import cap_lang.
Require Import machine_base.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import coqutil.Map.Interface.

Import ListNotations.

From QuickChick Require Import QuickChick.
Import QcNotation.

Open Scope Z.

Module GenCeriseSimple <: Gen DefCerise CerisePolicy CeriseLayout TSSCeriseDefault.
  Module MPC := TestMPC DefCerise CerisePolicy CeriseLayout TSSCeriseDefault.
  Import MPC.
  Import PrintCeriseSimple.
  
  Definition defFuel := 42%nat.

  Declare Instance chooseReg : (ChoosableFromInterval Register).
  
  Definition r0 : Register.
  Proof.
    assert ((0 <=? RegNum)%nat = true) by auto. 
    eexact (R 0 H).
  Defined.

  Definition ra : Register.
  Proof.
    assert ((1 <=? RegNum)%nat = true) by auto. 
    eexact (R 1 H).
  Defined.

  Definition sp : Register.
  Proof.
    assert ((2 <=? RegNum)%nat = true) by auto. 
    eexact (R 2 H).
  Defined.
    
  (*- TODO: Sometimes we might want to use/target ra and sp to inject/find bugs? *)
  Definition minRegN : nat := 3%nat.
  Definition minReg : Register.
  Proof.
    assert ((minRegN <=? RegNum)%nat = true) by auto.
    eexact (R 2 H).
  Defined.
  
  Definition noRegs  : nat := 8%nat.
  Definition maxRegN : nat := minRegN + noRegs - 1.
  Definition maxReg : Register.
  Proof.
    assert ((maxRegN <=? RegNum)%nat = true) by auto.
    eexact (R 2 H).
  Defined.
  
  Record PtrInfo := { pID     : RegName
                    ; pVal    : Z
                    ; pMinImm : Z
                    ; pMaxImm : Z
                    }.

  Definition showRegName (r:RegName) :=
    match r with
    | addr_reg.PC => "PC"
    | R n _ => ("r" ++ show n)%string
    end.

  Instance ShowRegName : Show RegName :=
    {| show r := showRegName r |}.
  
  Instance ShowPtrInfo : Show PtrInfo :=
    {| show p :=
         "{| " ++ "pID: " ++ show (pID p) ++ " ; "
               ++ "pVal: " ++ show (pVal p) ++ " ; "
               ++ "pMinImm: " ++ show (pMinImm p) ++ " ; "
               ++ "pMaxImm: " ++ show (pMaxImm p) ++ " ; "
    |}%string.

  Record ArithInfo := { aID : Register }.

  Record RegInfo := { dataPtr : list PtrInfo
                    ; loadPtr : list PtrInfo
                    ; badPtr  : list PtrInfo 
                    ; codePtr : list PtrInfo
                    ; arith : list ArithInfo
                    }.

  Definition Zseq (lo hi : Z) :=
    let len := Z.to_nat (Z.div (hi - lo) 4) in
    let fix aux start len :=
        match len with
        | 0%nat => []
        | S len' => start :: aux (start + 4) len'
        end in
    aux lo len.

  (*TODO: InstructionI -> instr *)
  Definition setInstrI addr (m : MachineState) (i : instr) : MachineState :=
    let '(regs,mem) := m in
    let mem' := gmap.gmap_partial_alter (fun _ => Some (machine_parameters.encodeInstrW i)) addr mem in
    (regs, mem').

  (*
    -- dataP, codeP : Predicates over the tagset to establish potential invariants for code/data pointers.
    -- Picks out valid (data registers + content + min immediate + max immediate + tag),
    --                 (jump registers + min immediate),
    --                 integer registers
   *)

  Fixpoint combine_match {A B} `{Show A} `{Show B}
           (l1 : list (Z * A)) (l2 : list (Z * B))
    : list (Z * A * B) :=
    match l1, l2 with
    | (z1,a)::l1',(z2,b)::l2' =>
      if Z.eqb z1 z2 then
        (z1, a, b) :: combine_match l1' l2'
      else exception ("combine_match - not_eq " ++ (show (l1, l2))%string)
    | nil, nil => nil
    | _, _ => exception ("combine_match: " ++ (show (l1,l2)))%string
    end.

  Definition genImm (n : Z) : G Z :=
    bindGen (choose (0, Z.div n 4))
            (fun n' => ret (Z.mul 4 n')).

  Definition genWord (n : Z) : G Word :=
    bindGen (genImm n)
            (fun n' => ret (inl n')).
  
  Definition genTargetReg (m : MachineState) : G Register :=
    choose (minReg, maxReg).

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ].

  Definition if_true_n (b:bool) (n:nat) :=
    if b then n else 0%nat.

  Print instr.
  
  (* TODO: Cheri-specific instructions *)
  Definition genInstr (i : LayoutInfo)
             (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl)
             (f : FunID)
    : G (instr * FunID * CodeAnnotation) :=
    freq [ (1%nat, ret (Fail, f, normal))
         (*TODO ; (prob, ret (legal offset from sp, f, normal)*)
         (*TODO ; (prob, ret (illegal offset from sp, f, normal)*)
         (*TODO ; (prob, ret (load, f, normal)*)
         (*TODO ; (prob, ret (store, f, normal)*)
         ].

  (* TODO: Cheri specific header sequence *)
  Definition headerSeq (offset : Z) (f nextF: FunID) :
    list (instr * FunID * CodeAnnotation) :=
    [ ].

  Axiom addrs_in_range_1 : forall z : Z, (z <=? MemNum) = true.
  Axiom addrs_in_range_2 : forall z : Z, (0 <=? z) = true.
  
  Definition genCall (l : LayoutInfo)
             (m : MachineState) (p : PolicyState)
             (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
             :
    option (G (list (instr * FunID * CodeAnnotation)))
    :=
(* TODO: repeat calls
   let existingSites :=
   List.map (fun '(i,t) => i - (word.unsigned (getPc m)))
   (List.filter (fun '(i,t) => callP t)
   (listify1 (memtags p))) in *)
      let newCallSites :=
          let offset_choices :=
              Zseq 20 (instHi l - instLo l - 50) in
          let valid_offsets :=
              List.filter (fun i =>
                             let pcval := flatten (option_map wtoa (gmap.gmap_lookup addr_reg.PC (fst m))) in
                             match pcval with
                             | Some a => Z.leb (a + i) (instHi l - 50)
                             | None => false
                             end) offset_choices in
          let not_used :=
              List.filter (fun i =>
                             match gmap.gmap_lookup (A i (addrs_in_range_1 i) (addrs_in_range_2 i)) (snd m) with
                             | Some _ => false
                             | None => true
                             end) valid_offsets in
          not_used in
(*      let exOpts :=
          (* Existing callsites, lookup fun id *)
          List.map (fun i => 
                      match map.get cm (word.unsigned (getPc m) + i) with
                      | Some _ =>
                        (headerHead i f) 
                      | _ => exception ("genCall - nofid: " ++ show (word.unsigned (getPc m) + i) ++ nl)%string
                      end) existingSites  in *)
      let newOpts :=
          List.map (fun i => headerSeq i f nextF) newCallSites in
      (* TODO: re-call *)
      match (* exOpts ++ *) newOpts with
      | [] => None
      | x :: xs =>
        Some (elems_ x (x :: xs))
      end.

  (* TODO: CHERI return sequence *)
  Definition returnSeq (f : FunID) :=
    [ (Fail, f, retrn) ].

  Definition genRetSeq (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (f : FunID) :=
    match gmap.gmap_lookup sp (fst m) with
    | Some spv =>
      (* See if spv - 12 is indeed a pc_depth *)
      Some (returnGen (returnSeq f))
    | _ => None
    end.
  
  Definition genInstrSeq
             (l : LayoutInfo)
             (m : MachineState) (p : PolicyState)
             (cm : CodeMap_Impl) (f nextF : FunID) :=
    let fromInstr :=
        bindGen (genInstr l m p cm f)
                (fun itf => returnGen ([itf])) in
    match genCall l m p cm f nextF,
          genRetSeq m p cm f with
    | None, None => fromInstr
    | None, Some g2 =>
      freq_ g2 ([ (5, fromInstr)
                ; (2, g2) ])%nat
    | Some g1, None =>
      freq_ g1 ([ (5, fromInstr)
                ; (2, g1) ])%nat
    | Some g1, Some g2 =>
      freq_ g1 ([ (5, fromInstr)
                ; (2, g1)
                ; (1, g2)
               ])%nat
  end.
  
  (* variantOf (fun k => fst c k = Sealed d) m n -> *)
  Definition genVariantOf (d : nat)
             (c : CtxState) (m : MachineState)
  : G MachineState :=
    foldGen (fun macc k =>
               (match fst c k with
                | Outside =>
                  returnGen macc
                | _ =>
                  bindGen (genImm 40) (fun z =>
                                         (ret (jorp macc k (inl z))))
                end)
            )
            (getComponents m) m .

  Definition genVariantByList (ks : list Component) (m : MachineState) : G MachineState :=
    foldGen (fun macc k =>
               match List.find (fun k' => keqb k k') ks with
               | Some _ => bindGen (genWord 40) (fun z => returnGen (jorp macc k z))
               | None => returnGen macc
               end)
            ks m.
  
  Definition get_cur_instr (m:MachineState) : option instr :=
    match option_map (fun a => (snd m) !m! a) (wtoa ((fst m) !r! addr_reg.PC)) with
    | Some (inl z) => Some (decodeInstr z)
    | _ => None
    end.

  Definition update_with_ifa (m0 m : MachineState) (cm : CodeMap_Impl)
             (inst : instr) (f : FunID) (a : CodeAnnotation) :
    (MachineState * MachineState * CodeMap_Impl) :=
    let m0' := option_map (fun a' => setInstrI a' m0 inst) (wtoa (fst m !r! addr_reg.PC)) in
    let m' := option_map (fun a' => setInstrI a' m inst) (wtoa (fst m !r! addr_reg.PC)) in
    let cm' := option_map (fun a' => map.put cm (z_of a') (Some a)) (wtoa (fst m !r! addr_reg.PC)) in
    match m0', m', cm' with
    | Some m0', Some m', Some cm' =>
      (m0', m', cm')
    | _, _, _ =>
      (m0, m, cm)
    end.
  
  (*
    -- | Generation by execution receives an initial machine state and
    -- | generates instructions until n steps have been executed.
    -- | Returns the original machines with just the instruction memory locations
    -- | updated.
   *)
  Fixpoint gen_exec_aux (steps : nat)
           (i : LayoutInfo)
           (m0 : MachineState)
           (m  : MachineState)
           (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
           (ifaseq : list (instr * FunID * CodeAnnotation))
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    match steps with
    | 0%nat =>
      (* Out-of-fuel: End generation. *)
      ret (m0, tt, cm)
    | S steps' =>
      match get_cur_instr m, ifaseq with
      | Some _, _::_ =>
        (* instr seq overlaps with previous instr: End generation *)
        ret (m0, tt, cm)
      | Some _, [] =>
        (* Instruction already exists, step... *)
        match mpstep (m,tt) with
        | Some ((m',_),o) =>
          (* ...and recurse. *)
          gen_exec_aux steps' i m0 m' cm f nextF ifaseq
        | _ =>
          (* Failstop: End generation *)
          ret (m0, tt, cm)
        end
      | _, [] =>
        bindGen (genInstrSeq i m tt cm f nextF)
                (fun ifaseq =>
                   match ifaseq with
                   | ((inst,f,a)::ifaseq) =>
                     let '(m0',m',cm') := update_with_ifa m0 m cm inst f a in
                     gen_exec_aux steps' i m0' m' cm f nextF ifaseq
                   | _ => ret (m0, tt, cm)
                   end)
      | _, (inst,f,a)::ifaseq' =>
        let '(m0',m',cm') := update_with_ifa m0 m cm inst f a in
        match mpstep (m', tt) with
        | Some ((m'', p''), o) =>
          let nextF' := if f =? nextF then nextF else (S nextF) in
          (gen_exec_aux steps' i m0' m'' cm' f nextF' ifaseq' )
        | _ =>
          (* Failstop: End generation *)
          (ret (m0', tt, cm'))
        end
      end
    end.

  Definition replicateGen {A} (n : nat) (g : G A) : G (list A) :=
    let fix aux n :=
        match n with
        | 0%nat => returnGen nil
        | S n' => liftGen2 cons g (aux n')
        end in
    aux n.

  Definition genGPRs
             (m : MachineState)
    : G (MachineState * PolicyState) :=
    bindGen (replicateGen (maxRegN - minRegN) (genWord 40)) (fun ds =>
    let '(i, m') :=
        List.fold_left (fun '(i,m) v =>
                          match n_to_regname i with
                          | Some r =>
                            (S i, update_reg m r v)
                          | None =>
                            (S i, m)
                          end)
                       ds (minRegN, m) in
    returnGen (m', tt)).

  Definition genDataMemory (i : LayoutInfo) (m : MachineState) : G (MachineState * PolicyState) :=
    let idx := Zseq (dataLo i) (dataHi i) in
    bindGen (replicateGen (List.length idx) (genWord 40))
            (fun vals =>
               let '(i, m') :=
                   List.fold_left (fun '(i,m) v =>
                                     match z_to_addr i with
                                     | Some a =>
                                       (i+1, update_mem m a v)
                                     | None =>
                                       (i+1, m)
                                     end)
                                  vals (dataLo i, m) in
               ret (m', tt)).
  
  Definition genMachine
             (i : LayoutInfo)
             (m0 : MachineState)
             (cm0 : CodeMap_Impl)
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    (*  
        genMachine :: PolicyPlus -> (PolicyPlus -> Gen TagSet) -> (PolicyPlus -> Gen TagSet) ->
        (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
        (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
        (Instr_I -> Gen TagSet) -> TagSet -> 
        Gen RichState
        genMachine pplus genMTag genGPRTag dataP codeP callP headerSeq retSeq genITag spTag = do
     *)
    bindGen (genDataMemory i m0)
            (fun '(ms,ps) =>
               bindGen (genGPRs ms)
                       (fun '(ms', ps') =>
                          (* Something about sp?
                             let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
                             ps' <- genGPRTs pplus ps (genGPRTag pplus)
                             let ps'' = ps' & pgpr . at sp ?~ spTag
                           *)
                          (gen_exec_aux defFuel i ms' ms' cm0 0%nat 1%nat
                                        nil))).
  
  Definition genMach :=
    genMachine defLayoutInfo (empty,empty) map.empty.

End GenCeriseSimple.