From StackSafety Require Import MachineModule PolicyModule TestingModules
     CeriseMachine CeriseLayout TestSubroutineSimple PrintCeriseSimple.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List.

Require Import ZArith. Open Scope Z.
Require Import cap_machine.addr_reg.
Require Import machine_base.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Import ListNotations.

Module GenCeriseSimple <: Gen DefCerise CerisePolicy CeriseLayout TSSCeriseDefault.
  Module MPC := TestMPC DefCerise CerisePolicy CeriseLayout TSSCeriseDefault.
  Import MPC.
  Import PrintCeriseSimple.
  
  Definition defFuel := 42%nat.
  
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
  Definition minReg : nat := 8%nat.
  Definition noRegs : nat := 3%nat.
  Definition maxReg : nat := minReg + noRegs - 1.
  
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
  Definition setInstrI addr (m : MachineState) (i : InstructionI) : MachineState :=
    let prog := [encode i] in
    withXAddrs
      (addXAddrRange addr (4 * Datatypes.length prog)
                     (getXAddrs m))
      (withMem
         (unchecked_store_byte_list addr
                                    (Z32s_to_bytes prog) (getMem m)) m).

  (*
    -- dataP, codeP : Predicates over the tagset to establish potential invariants for code/data pointers.
    -- Picks out valid (data registers + content + min immediate + max immediate + tag),
    --                 (jump registers + min immediate),
    --                 integer registers
   *)

    Definition listify1 {A} (m : Zkeyed_map A)
    : list (Z * A) :=
    List.rev (map.fold (fun acc z v => (z,v) :: acc) nil m).
  
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

  Definition listify2 {A B} `{Show A} `{Show B}
             (m1 : Zkeyed_map A)
             (m2 : Zkeyed_map B) : list (Z * A * B) :=
    combine_match (listify1 m1) (listify1 m2).
  
  Definition groupRegisters (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (dataP codeP : TagSet -> bool)
    : RegInfo :=
    let regs := getRegs m in
    let tags := regtags p in

    (* Given range limits (low / high) for when something
       is valid, calculate the immediates involved. *)
    let getInfo (regTagP : TagSet -> bool) lo hi rID rVal rTag :=
        if andb (regTagP rTag) (rVal <=? hi) then
          let minToAdd :=
              if rVal <=? lo then lo - rVal else 0 in
          Some {| pID := rID; pVal := rVal
                ; pMinImm := minToAdd
                ; pMaxImm := hi - rVal
                ; pTag := rTag 
               |}
        else None
    in

    let noSp p t :=
        andb (p t) (negb (existsb (tag_eqb Tsp) t)) in
    let getDataInfo :=
        getInfo (noSp dataP) (stackLo i) (stackHi i) in 
    let getCodeInfo :=
        getInfo (noSp codeP) (instLo i) (instHi i) in
    let isStackLoc p t :=
        (*      trace ("Testing Loc: " ++ show t ++ nl)%string *)
        (
          andb (p t) (match t with
                      | [Tstack _] => true
                      | _ => false
                      end)) in
    let loadLocs :=
        List.fold_right
          (fun (i : Z) '(acc1,acc2) =>
             match pctags p, map.get (memtags p) i with
             | [Tpc pcdepth], Some (cons (Tstack depth) nil) =>
               (* TODO: Likely to load bad stuff? *)
               if Nat.leb pcdepth depth  then 
                 (i :: acc1, acc2)
               else (acc1, i::acc2)
             | _, _ => (acc1, acc2)
             end
          ) (nil,nil) (Zseq (stackLo i) (stackHi i)) in
                         
    let getLoadInfo proj (regTagP : TagSet -> bool)
                    rID rVal rTag :=
        (*      trace ("Getting load info: " ++ show rID ++ " " ++ show (regTagP rTag) ++ " " ++ show loadLocs ++ nl)%string *)
        (if (regTagP rTag) then
           List.map (fun loc =>
                       {| pID := rID; pVal := rVal
                        ; pMinImm := 0
                        ; pMaxImm :=  loc - rVal
                        ; pTag := rTag 
                       |}) (proj loadLocs)
         else nil)
    in
    let processRegs f :=
        List.fold_right
          (fun '(rID, rVal, rTag) acc =>
             (*           trace ("Processing: " ++ show (rID, rVal, rTag) ++ nl)*) (
               match f rID (word.signed rVal) rTag with
               | Some pi =>
                 pi :: acc
               | None => acc
               end)) nil (listify2 regs tags) in
    
    let processRegsList f :=
        List.fold_right
          (fun '(rID, rVal, rTag) acc =>
             (*           trace ("Processing: " ++ show (rID, rVal, rTag) ++ nl)%string *)
             (
               if Z.eqb rID 2 then
                 f rID (word.signed rVal) rTag ++ acc
                   
               else acc
                   
          )) nil (listify2 regs tags) in

    let dataRegs := processRegs getDataInfo in
    let loadRegs := processRegsList (getLoadInfo fst dataP) in
    let badRegs  := processRegsList (getLoadInfo snd dataP) in  
    let codeRegs := processRegs getCodeInfo in
    let arithRegs :=
        List.fold_right
          (fun '(rID, rVal, rTag) acc =>
             if noSp (fun _ => true) rTag then
               {| aID := rID |} :: acc
             else acc) nil (listify2 regs tags) in
  
    {| codePtr := codeRegs
     ; dataPtr := dataRegs
     ; arith   := arithRegs
     ; loadPtr := loadRegs
     ; badPtr  := badRegs                  
    |}.

  Definition genImm (n : Z) : G Z :=
    bindGen (choose (0, Z.div n 4))
            (fun n' => ret (Z.mul 4 n')).

  (* TODO: RegName generator *)
  Definition genTargetReg (m : MachineState) : G Register :=
    choose (minReg, maxReg).

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ].
  (*
    -- TODO: This might need to be further generalized in the future
    genInstr :: PolicyPlus -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Instr_I -> Gen TagSet) -> Gen (Instr_I, TagSet)
   *)
  (* TODO: InstructionI -> instr *)
  Definition genInstr (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl)
             (dataP codeP : TagSet -> bool) (f : FunID)
             (genInstrTag : InstructionI -> G TagSet)
    : G (InstructionI * TagSet * FunID * CodeAnnotation) :=
    let groups := groupRegisters i t m p dataP codeP in
    let a := arith groups in
    let d := dataPtr groups in
    let c := codePtr groups in
    let l := loadPtr groups in
    (*  trace ("Grouped loads: " ++ show l ++ nl)%string *)
    (  
      let def_a := {| aID := 0 |} in
      let def_dp := {| pID := 0; pVal := 0;
                       pMinImm := 0; pMaxImm := 0;
                       pTag := dataTag t
                    |} in

      (*  trace (show (l, badPtr groups)%string) *)
      (
        let onNonEmpty {A} (l : list A) n :=
            match l with
            | [] => O
            | _  => n
            end in
        freq [ (onNonEmpty a 1%nat,
                bindGen (elems_ def_a a) (fun ai =>
                bindGen (genTargetReg m) (fun rd =>
                bindGen (genImm (dataHi i)) (fun imm =>
                let instr := Addi rd (aID ai) imm in
                bindGen (genInstrTag instr) (fun tag =>
                ret (instr, tag, f, normal))))))
             ;  (3%nat, match map.get (getRegs m) sp with
                        | Some spVal' =>
                          let spVal := word.unsigned spVal' in
                          let minImm := spVal - stackLo i in
                          let maxImm := stackHi i - spVal in
                          bindGen (genImm (maxImm - minImm)) (fun imm' =>
                          let imm := minImm + imm' in
                          bindGen (genTargetReg m) (fun rd =>
                          let instr := Lw rd sp imm in
                          bindGen (genInstrTag instr) (fun tag =>
                          ret (instr, tag, f, normal))))

                        | _ => exception "No sp?"
                        end)
  (*         ; (onNonEmpty l 3%nat,
            trace (show (l, badPtr groups))
         (bindGen (elems_ l ([l; badPtr groups])) (fun l' =>
          bindGen (elems_ def_dp l') (fun pi =>
          bindGen (genTargetReg m) (fun rd =>
          let imm := pMaxImm pi in 
          (*trace ("Generating... " ++ show (imm, pMaxImm pi))%string *)
          (let instr := Lw rd (pID pi) imm in
          bindGen (genInstrTag instr) (fun tag =>
          ret (instr, tag, f, normal))))))))
*)
             ;  ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
                 bindGen (elems_ def_dp d) (fun pi =>
                 bindGen (genSourceReg m) (fun rs =>
                 bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
                 let imm := pMinImm pi + imm' in
                 let instr := Sw (pID pi) rs imm in
                 bindGen (genInstrTag instr) (fun tag => 
                 ret (instr, tag, f, normal)))))) 
             ;   (onNonEmpty a 1%nat,
                  bindGen (elems_ def_a a) (fun ai1 =>
                  bindGen (elems_ def_a a) (fun ai2 =>
                  bindGen (genTargetReg m) (fun rd =>
                  let instr := Add rd (aID ai1) (aID ai2) in
                  bindGen (genInstrTag instr) (fun tag => 
                  ret (instr, tag, f, normal))))))
    ])).
(*
-- TODO: Uncomment this and add stack.dpl rule
--            , (onNonEmpty arithInfo 1,
--               do -- BLT
--                  AI rs1 <- elements arithInfo
--                  AI rs2 <- elements arithInfo
--                  imm <- (8+) <$> genImm 12 --TODO: More principled relative jumps
--                  -- BLT does multiples of 2
--                  let instr = BLT rs1 rs2 imm
--                  tag <- genInstrTag instr
--                  return (instr, tag)
--              )
            ]
 *)

  Definition headerHead offset f :
    list (InstructionI * TagSet * FunID * CodeAnnotation) := [(Jal ra offset , [Tinstr; Tcall], f    , call)].

  (* TODO: Cheri specific header sequence *)
  Definition headerSeq offset f nextF :
    list (InstructionI * TagSet * FunID * CodeAnnotation) :=
    headerHead offset f ++
               [ (Addi sp sp 12 , [Tinstr; Th1]  , nextF, normal)
               ; (Sw sp ra 0    , [Tinstr; Th2]  , nextF, normal)
               ; (Sw sp 8 (-8) , [Tinstr; Th3]  , nextF, normal)
               ; (Sw sp 9 (-4) , [Tinstr; Th4]  , nextF, normal)        
               ].
  
  (* Based on Rob's 
     (* 08 *) IInstruction (Sw SP RA 0); (* H1 *)
     (* 12 *) IInstruction (Addi SP SP 12); (* H2 *)
   *)
  Definition genCall (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
             (callP :  TagSet -> bool) :
    option (G (list (InstructionI * TagSet * FunID * CodeAnnotation)))
    :=
      (*  
          genCall :: PolicyPlus -> Machine_State -> PIPE_State ->
          (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
          (Instr_I -> Gen TagSet) ->
          (Integer -> [(Instr_I, TagSet)]) ->
          Gen [(Instr_I, TagSet)]
          genCall pplus ms ps dataP codeP callP genInstrTag headerSeq = do
          let m = ms ^. fmem
          t = Map.assocs $ ps ^. pmem
       *)
      let existingSites :=
          List.map (fun '(i,t) => i - (word.unsigned (getPc m)))
                   (List.filter (fun '(i,t) => callP t)
                                (listify1 (memtags p))) in
      let newCallSites :=
          let offset_choices :=
              Zseq 20 (instHi l - instLo l - 50) in
          let valid_offsets :=
              List.filter (fun i => Z.leb (word.unsigned (getPc m) + i) (instHi l - 50)) offset_choices in
          let not_used :=
              List.filter (fun i =>
                             match map.get (getMem m) (word.of_Z i) with
                             | Some _ => false
                             | None => true
                             end) valid_offsets in
          not_used in
      let exOpts :=
          (* Existing callsites, lookup fun id *)
          List.map (fun i => 
                      match map.get cm (word.unsigned (getPc m) + i) with
                      | Some _ =>
                        (headerHead i f) 
                      | _ => exception ("genCall - nofid: " ++ show (word.unsigned (getPc m) + i) ++ nl)%string
                      end) existingSites  in
      let newOpts :=
          List.map (fun i => headerSeq i f nextF) newCallSites in
      (* TODO: re-call *)
      match (* exOpts ++ *) newOpts with
      | [] => None
      | x :: xs =>
        Some (elems_ x (x :: xs))
      end.

  
  Definition returnSeq (f rf : FunID) :=
    [ (Lw   ra sp 0     , [Tinstr; Tr1], f, normal)
    ; (Addi sp sp (-12) , [Tinstr; Tr2], f, normal)
    ; (Jalr ra ra 0     , [Tinstr; Tr3], rf, retrn)
    ].

  Definition genRetSeq (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (f : FunID) :=
    match map.get (getRegs m) sp with
    | Some spv =>
      (* See if spv - 12 is indeed a pc_depth *)
      match map.get (memtags p) (word.unsigned spv) with
      | Some (cons (Tpc depth) nil) =>
        Some (returnGen (returnSeq f depth))
      | _ => None
      end
    | _ => None
    end.
  
  Definition genInstrSeq
             (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (dataP codeP callP : TagSet -> bool)
             (cm : CodeMap_Impl) (f nextF : FunID)
             (genInstrTag : InstructionI -> G TagSet) :=
    let fromInstr :=
        bindGen (genInstr l t m p cm dataP codeP f genInstrTag)
                (fun itf => returnGen ([itf])) in
    match genCall l t m p cm f nextF callP,
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
               (*trace (show ("Varying:", k, fst c k)) *)
               (match fst c k with
                | Outside =>
                  returnGen macc
                | _ =>
                  bindGen (genImm 40) (fun z =>
                                         (*               trace ("Trying to set: " ++ show k ++ " to " ++ show z ++ " which was " ++ show (fst c k) ++ nl ++ "Previous value was: " ++ show (proj macc k) ++ nl ++ " Next value will be: " ++ show (proj (jorp macc k z) k) ++ nl ++ "Nearby values are: " ++ show (kplus k) ++ " : " ++ show (proj macc (kplus k)) ++ " and " ++ show (ksub k) ++ " : " ++ show (proj macc (ksub k)) ++ nl)%string *)
                                         (returnGen (jorp macc k z)))
                end)
            )
            (getComponents m) m .

  (*
    -- | Generation by execution receives an initial machine X PIPE state and
    -- | generates instructions until n steps have been executed.
    -- | Returns the original machines with just the instruction memory locations
    -- | updated.
    genByExec :: PolicyPlus -> Int -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
    (Instr_I -> Gen TagSet) -> 
    Gen (Machine_State, PIPE_State)
   *)
  Fixpoint gen_exec_aux (steps : nat)
           (i : LayoutInfo) (t : TagInfo)
           (m0 : MachineState) (p0 : PolicyState)
           (m  : MachineState) (p  : PolicyState)
           (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
           (its : list (InstructionI * TagSet * FunID * CodeAnnotation))
           (dataP codeP callP : TagSet -> bool)
           (genInstrTag : InstructionI -> G TagSet)
    (* num calls? *)
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    (*  trace (show ("GenExec...", steps, its, printPC m p) ++ nl)%string *)
    (match steps with
     | O =>
       (* Out-of-fuel: End generation. *)
       ret (m0, p0, cm)
     | S steps' =>
       match map.get (getMem m) (getPc m) with
       | Some _ =>
         match its with
         | nil =>
           (*      trace ("Existing instruction found: " ++ nl)%string *)
           (            
             (* Instruction already exists, step... *)
             match mpstep (m,p) with
             | Some ((m',p'),o) =>
               (* ...and recurse. *)
               gen_exec_aux steps' i t m0 p0 m' p' cm f nextF its codeP dataP callP genInstrTag
             | _ =>
               (* ... something went wrong. Trace something? *)
               ret (m0, p0, cm)
             end
           )
         | _ =>
           (*trace ("Existing instruction mid-sequence" ++ nl)%string*)
           (ret (m0, p0, cm))
         end
       | _ =>
         (*      trace ("No instruction found " ++ nl)%string *)
         (* Check if there is anything left to put *)
         (bindGen (match its with
                   | [] =>
                     (* Generate an instruction sequence. *)
                     (* TODO: Sequences, calls. *)
                     bindGen (genInstrSeq i t m p dataP codeP callP cm f nextF genInstrTag)
                             (fun itfas =>
                                match itfas with
                                | (i,t,f',a) :: itfs' =>
                                  (*                              trace (show (f',ist, ists') ++ nl)%string*)
                                  (returnGen (a, f', (i,t), itfs'))
                                | _ => exception "EmptyInstrSeq"
                                end)
                   | ((i,t,f',a)::itfs') =>
                     returnGen (a, f', (i,t), itfs')
                   end)
                  (fun '(a, f', (is,it), its) =>
                     let nextF' := if Nat.eqb f' nextF then
                                     S nextF else nextF in
                     let m0' := setInstrI (getPc m) m0 is in
                     let m'  := setInstrI (getPc m) m  is in
                     let p0' := setInstrTagI (word.unsigned (getPc m)) p0 it in
                     let p'  := setInstrTagI (word.unsigned (getPc m)) p it in
                     let cm' := map.put cm (word.unsigned (getPc m)) (Some a) in
                     match mpstep (m', p') with
                     | Some ((m'', p''), o) =>
                       (*            trace ("PC after mpstep: " ++ show (word.unsigned (getPc m'')) ++ nl)%string  *)
                       (gen_exec_aux steps' i t m0' p0' m'' p'' cm' f' nextF' its dataP codeP callP genInstrTag)
                     | _ =>
                       (*           trace ("Couldn't step" ++ nl ++  printMachine m' p' cm' ++ nl)%string *)
                       (ret (m0', p0', cm'))
                     end))
       end
     end).

  Definition replicateGen {A} (n : nat) (g : G A) : G (list A) :=
    let fix aux n :=
        match n with
        | O => returnGen nil
        | S n' => liftGen2 cons g (aux n')
        end in
    aux n.
  
  Definition genGPRs (t : TagInfo)
             (m : MachineState) (p : PolicyState)
    : G (MachineState * PolicyState) :=
    bindGen (replicateGen 3 (genImm 40)) (fun ds =>
    bindGen (replicateGen 3 (returnGen (regTag t))) (fun ts =>
    let regs :=
        List.fold_left (fun '(i,m) r =>
                          (i+1, map.put m i (word.of_Z r)))
                       ds (minReg, getRegs m) in
    let tags : Z * TagMap :=
        List.fold_left (fun '(i,m) (t : TagSet) =>
                          (i+1, map.put m i t))
                       ts (minReg, regtags p) in
    returnGen (withRegs (snd regs) m,
               p <| regtags := snd tags |>))).

  Definition genDataMemory
             (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
    : G (MachineState * PolicyState) :=
    let idx := Zseq (dataLo i) (dataHi i) in
    bindGen (replicateGen (List.length idx) (genImm (dataHi i))) (fun vals =>           
    bindGen (replicateGen (List.length idx) (returnGen (dataTag t))) (fun tags =>           
    returnGen (withXAddrs
                 (addXAddrRange (word.of_Z (dataLo i))
                                (4 * Datatypes.length vals)
                                (getXAddrs m))
                 (withMem
                    (unchecked_store_byte_list (word.of_Z (dataLo i))
                                               (Z32s_to_bytes vals) (getMem m)) m),
               p <| memtags := 
                 List.fold_right
                   (fun '(z,t) pmem => map.put pmem z t)
                   (memtags p) (List.combine idx tags) |>))).

  
  Definition genMachine
             (i : LayoutInfo) (t : TagInfo)
             (m0 : MachineState) (p0 : PolicyState)
             (cm0 : CodeMap_Impl)
             (dataP codeP callP : TagSet -> bool)
             (genInstrTag : InstructionI -> G TagSet)
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    (*  
        genMachine :: PolicyPlus -> (PolicyPlus -> Gen TagSet) -> (PolicyPlus -> Gen TagSet) ->
        (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
        (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
        (Instr_I -> Gen TagSet) -> TagSet -> 
        Gen RichState
        genMachine pplus genMTag genGPRTag dataP codeP callP headerSeq retSeq genITag spTag = do
     *)
    bindGen (genDataMemory i t m0 p0)
            (fun '(ms,ps) =>
               bindGen (genGPRs t ms ps)
                       (fun '(ms', ps') =>
                          (* Something about sp?
                             let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
                             ps' <- genGPRTs pplus ps (genGPRTag pplus)
                             let ps'' = ps' & pgpr . at sp ?~ spTag
                           *)
                          (gen_exec_aux defFuel i t ms' ps' ms' ps' cm0 O (S O)
                                        nil dataP codeP callP genInstrTag))).

  Definition zeroedRiscvMachine: RiscvMachine := {|
    getRegs :=
      List.fold_right (fun '(i,v) m => map.put m i (word.of_Z v))
                      map.empty
                      ([ (0, 0)
                         ; (1, 0)   (* ra *)
                         ; (2, 500) (* sp *)
                      ]);
    getPc := ZToReg 0;
    getNextPc := ZToReg 4;
    getMem := unchecked_store_byte_list
                (word.of_Z 500)
                (Z32s_to_bytes (repeat 0 125))
                map.empty;
    (*unchecked_store_byte_list (word.of_Z 500)
      (Z32s_to_bytes (cons 0 nil))
      (map.empty); *)
    getXAddrs := nil; 
    getLog := nil;
                                                |}.

  
  Definition zeroedPolicyState : PolicyState :=
    {| nextid := 0
       ; pctags := [Tpc 0]
       ; regtags :=
           List.fold_right (fun '(i,v) m => map.put m i v)
                           map.empty
                           ([ (0, [])
                              ; (1, [])   (* ra *)
                              ; (2, [Tsp]) (* sp *)
                           ])
       ; memtags :=
           (map.put 
              (snd (List.fold_right (fun x '(i,m) => (i+4, map.put m i x)) (500, map.empty)
                                    (repeat nil 125)))
              500
              ([Tstack 0]))
             (*map.empty (* map.put map.empty 500 (cons Tsp nil) *)*)
    |}. 
  
  Definition genMach :=
  let codeP := fun tt => true in
  let dataP := fun tt => true in
  (* Fix this *)
  let callP := fun tt =>
                 existsb (fun t => match t with
                                   | Th1 => true
                                   | _ => false
                                   end) tt in  
  let genInstrTag : InstructionI -> G TagSet :=
      fun i => returnGen (cons Tinstr nil) in
  genMachine defLayoutInfo defTagInfo zeroedRiscvMachine zeroedPolicyState map.empty
             dataP codeP callP genInstrTag.
End GenRISCVTagSimple.
