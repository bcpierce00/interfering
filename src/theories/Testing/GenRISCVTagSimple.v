From StackSafety Require Import MachineModule PolicyModule TestingModules
     RISCVMachine Lazy DefaultLayout PrintRISCVTagSimple.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import ZArith. Open Scope Z.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import coqutil.Word.Properties.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Import ListNotations.

(*Module GenRISCVLazyFixed <: Gen RISCV TPLazyFixed DLObs TSSRiscvDefault.
  Module MPC := TestMPC RISCVObs TPLazyFixed DLObs TSSRiscvDefault.
  Import MPC.
  Import PrintRISCVLazyFixed.

  Definition maxFuel := 100%nat.
  Definition funMaxFuel := 10%nat.

  Definition r0 : Register := 0.
  Definition ra : Register := 1.
  Definition sp : Register := 2.
  
  (*- TODO: Sometimes we might want to use/target ra and sp to inject/find bugs? *)
  Definition minReg : Register := 8.
  Definition noRegs : nat := 3%nat.
  Definition maxReg : Register := minReg + Z.of_nat noRegs - 1.
  
  Record TagInfo :=
    { regTag  : TagSet
    ; codeTag : TagSet
    ; dataTag : TagSet 
    ; pcTag   : TagSet
    }.

  Definition defTagInfo :=
    {| regTag  := nil
     ; codeTag := [Tinstr]
     ; dataTag := nil                    
     ; pcTag   := [Tpc 0]
    |}.

  Record PtrInfo := { pID     : Register
                    ; pVal    : Z
                    ; pMinImm : Z
                    ; pMaxImm : Z
                    ; pTag : TagSet
                    }.

  Instance ShowPtrInfo : Show PtrInfo :=
    {| show p :=
         "{| " ++ "pID: " ++ show (pID p) ++ " ; "
               ++ "pVal: " ++ show (pVal p) ++ " ; "
               ++ "pMinImm: " ++ show (pMinImm p) ++ " ; "
               ++ "pMaxImm: " ++ show (pMaxImm p) ++ " ; "
               ++ "pTag: " ++ show (pTag p) ++ " |}"
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
        | O => []
        | S len' => start :: aux (start + 4) len'
        end in
    aux lo len.
    
  Definition setInstrI addr (m : MachineState) (i : InstructionI) : MachineState :=
    let prog := [encode i] in
    withXAddrs
      (addXAddrRange addr (4 * Datatypes.length prog)
                     (getXAddrs m))
      (withMem
         (unchecked_store_byte_list addr
                                    (Z32s_to_bytes prog) (getMem m)) m).

  Definition setInstrTagI addr (p : PolicyState) (t : TagSet) : PolicyState :=
    p <| memtags := map.put (memtags p) addr t |>.

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
    if (n >=? 0)
    then bindGen (choose (0, Z.div n 4))
                 (fun n' => ret (Z.mul 4 n'))
    else ret 0.

  Definition genTargetReg (m : MachineState) : G Register :=
    choose (minReg, maxReg).

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ].

  Definition if_true_n (b:bool) (n:nat) :=
    if b then n else O.
  
  Definition genStackbasedWrite (i : LayoutInfo) (m : MachineState) : G InstructionI :=
    let spVal := projw m (Reg SP) in
    bindGen (genSourceReg m)
            (fun rs =>
               freq [ (10%nat, ret (Sw sp rs (-4)))
                    ; (10%nat, ret (Sw sp rs (-8)))
                    ; (if_true_n (512 <? spVal) 1%nat, ret (Sw sp rs (-12)))
                    ; (if_true_n (516 <? spVal) 2%nat, (ret (Sw sp rs (-16))))
                    ; (if_true_n (520 <? spVal) 2%nat, (ret (Sw sp rs (-20))))
                    ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                      (fun off => ret (Sw sp rs (- off))))
                    ; (1%nat, bindGen (choose (0, 600 - spVal))
                                      (fun off => ret (Sw sp rs off)))
            ]).

    Definition genStackbasedRead (i : LayoutInfo) (m : MachineState) : G InstructionI :=
      let spVal := projw m (Reg SP) in
      bindGen (genTargetReg m)
              (fun rd =>
                 freq [ (10%nat, ret (Lw rd sp (-4)))
                      ; (10%nat, ret (Lw rd sp (-8)))
                      ; (if_true_n (512 <? spVal) 1%nat, ret (Lw rd sp (-12)))
                      ; (if_true_n (516 <? spVal) 2%nat, ret (Lw rd sp (-16)))
                      ; (if_true_n (520 <? spVal) 2%nat, ret (Lw rd sp (-20)))
                      ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                        (fun off => ret (Lw rd sp (- off))))
                      ; (1%nat, bindGen (choose (0, 600 - spVal))
                                      (fun off => ret (Lw rd sp off)))
              ]).

  (*
    -- TODO: This might need to be further generalized in the future
    genInstr :: PolicyPlus -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Instr_I -> Gen TagSet) -> Gen (Instr_I, TagSet)
   *)
  Definition genInstr (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl)
             (dataP codeP : TagSet -> bool) (f : FunID)
    : G (InstructionI * TagSet * FunID * Operations) :=
    let groups := groupRegisters i t m p dataP codeP in
    let a := arith groups in
    let d := dataPtr groups in
    let c := codePtr groups in
    let l := loadPtr groups in
    (*  trace ("Grouped loads: " ++ show l ++ nl)%string *)
    let def_a := {| aID := 0 |} in
    let def_dp := {| pID := 0; pVal := 0;
                     pMinImm := 0; pMaxImm := 0;
                     pTag := dataTag t
                  |} in

      (*  trace (show (l, badPtr groups)%string) *)
    let onNonEmpty {A} (l : list A) n :=
        match l with
        | [] => O
        | _  => n
        end in
    let noops : Operations := [] in
    freq [ (onNonEmpty a 1%nat,
            bindGen (elems_ def_a a) (fun ai =>
            bindGen (genTargetReg m) (fun rd =>
            bindGen (genImm (dataHi i)) (fun imm =>
            let instr := Addi rd (aID ai) imm in
            ret (instr, [Tinstr], f, noops)))))
         ; (4%nat, bindGen (genStackbasedWrite i m)
                           (fun instr =>
                              (ret (instr, [Tinstr], f, noops))))
         ; (4%nat, bindGen (genStackbasedRead i m)
                           (fun instr =>
                              ret (instr, [Tinstr], f, noops)))
(*           ;  (3%nat, match map.get (getRegs m) sp with
                      | Some spVal' =>
                        let spVal := word.unsigned spVal' in
                        let minImm := spVal - stackLo i in
                        let maxImm := stackHi i - spVal in
                        bindGen (genImm (maxImm - minImm)) (fun imm' =>
                        let imm := minImm + imm' in
                        bindGen (genTargetReg m) (fun rd =>
                        let instr := Lw rd sp imm in
                        ret (instr, [Tinstr], f, normal)))

                      | _ => exception "No sp?"
                      end)*)
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
(*             ;  ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
                 bindGen (elems_ def_dp d) (fun pi =>
                 bindGen (genSourceReg m) (fun rs =>
                 bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
                 let imm := pMinImm pi + imm' in
                 let instr := Sw (pID pi) rs imm in
                 ret (instr, [Tinstr], f, normal))))) *)
           ;   (onNonEmpty a 1%nat,
                bindGen (elems_ def_a a) (fun ai1 =>
                bindGen (elems_ def_a a) (fun ai2 =>
                bindGen (genTargetReg m) (fun rd =>
                let instr := Add rd (aID ai1) (aID ai2) in
                ret (instr, [Tinstr], f, noops)))))
    ].

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

  (* FIXME Code annotations are replaced by operations, but only the constructor
     carries meaning! *)
  Definition callHead offset f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Jal ra offset, [Tinstr; Tcall], f, [(Call f [] [])])].

  Definition headerHead f:
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Sw sp ra 0, [Tinstr; Th1], f, [(*noops*)])].

  Definition initSeq f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [  (Addi sp sp 12 , [Tinstr; Th2], f, [(*noops*)])
(*       (Sw sp 8 (-8)  , [Tinstr]     , f, normal);
       (Sw sp 9 (-4)  , [Tinstr]     , f, normal)*)
    ].
  
  Definition callSeq offset f nextF :=
    callHead offset f ++ headerHead nextF ++ initSeq nextF.
  
  (* Based on Rob's 
     (* 08 *) IInstruction (Sw SP RA 0); (* H1 *)
     (* 12 *) IInstruction (Addi SP SP 12); (* H2 *)
   *)
  Definition genCall (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
             (callP :  TagSet -> bool) :
    option (G (list (InstructionI * TagSet * FunID * Operations)))
    :=
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
                        callHead i f
                      | _ => exception ("genCall - nofid: " ++ show (word.unsigned (getPc m) + i) ++ nl)%string
                      end) existingSites  in
      let newOpts :=
          List.map (fun i => callSeq i f nextF) newCallSites in
      match exOpts ++ newOpts with
      | [] => None
      | x :: xs =>
        Some (elems_ x (x :: xs))
      end.
  
  Definition returnSeq (f : FunID) :=
    [ (Addi sp sp (-12) , [Tinstr; Tr1], f, [(*noops*)])
    ; (Lw   ra sp 0     , [Tinstr; Tr2], f, [(*noops*)])
    ; (Jalr ra ra 0     , [Tinstr; Tr3], f, [Return])
    ].

  Definition genRetSeq (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (f : FunID) :=
    let spv := projw m (Reg sp) in
    if (512 <? spv)%Z 
    then Some (returnGen (returnSeq f))
    else None.

  Definition genInstrSeq
             (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (dataP codeP callP : TagSet -> bool)
             (cm : CodeMap_Impl) (f nextF : FunID)
             (fSteps : list nat)
    : G (list (InstructionI * TagSet * FunID * Operations) * (list nat)) :=
    let fromInstr :=
        bindGen (genInstr l t m p cm dataP codeP f)
                (fun itf => returnGen ([itf])) in
    let '(fFuel, rest) :=
        match fSteps with
        | (S fFuel)::rest => (fFuel, rest)
        | O::rest => (O, rest)
        | _ => (O, [])
        end in
    let returnFreq := (funMaxFuel - fFuel)%nat in
    let instrFreq := (fFuel - 2)%nat in
    let callFreq := 1%nat in
    let instGen := bindGen fromInstr (fun g => ret (g,fFuel::rest)) in
    match genCall l t m p cm f nextF callP,
          genRetSeq m p cm f with
    | None, None => instGen
    | None, Some g2 =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest))) ])%nat
    | Some g1, None =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest))) ])%nat
    | Some g1, Some g2 =>
      freq_ instGen ([ (instrFreq, bindGen fromInstr (fun g => ret (g,fFuel::rest)))
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest)))
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest)))
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
                                         (*               trace ("Trying to set: " ++ show k ++ " to " ++ show z ++ " which was " ++ show (fst c k) ++ nl ++ "Previous value was: " ++ show (proj macc k) ++ nl ++ " Next value will be: " ++ show (proj (jorp macc k z) k) ++ nl ++ nl)%string *)
                                         (returnGen (jorp macc k z)))
                end)
            )
            (getElements m) m .

  Definition genVariantByList (ks : list Element) (m : MachineState) : G MachineState :=
    foldGen (fun macc k =>
               match List.find (fun k' => keqb k k') ks with
               | Some _ => bindGen (genImm 40) (fun z => returnGen (jorp macc k z))
               | None => returnGen macc
               end)
          ks m.

  Instance ShowStuff : Show (InstructionI * TagSet * FunID * Operations) :=
    {| show '(i, ts, f, a) := (show i ++ "@" ++ show ts ++ "|" ++ show f)%string |}.
  
  (*
    -- | Generation by execution receives an initial machine X PIPE state and
    -- | generates instructions until n steps have been executed.
    -- | Returns the original machines with just the instruction memory locations
    -- | updated.
    genByExec :: PolicyPlus -> Int -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
    Gen (Machine_State, PIPE_State)
   *)
  Fixpoint gen_exec_aux (steps : nat)
           (funSteps : list nat)
           (i : LayoutInfo) (t : TagInfo)
           (m0 : MachineState) (p0 : PolicyState)
           (m  : MachineState) (p  : PolicyState)
           (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
           (its : list (InstructionI * TagSet * FunID * Operations))
           (dataP codeP callP : TagSet -> bool)
    (* num calls? *)
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    (*trace ("GenExec..." ++ show steps ++ " " ++ show its ++ printPC m p ++ nl)%string*)
    match steps with
    | O =>
      (* Out-of-fuel: End generation. *)
      ret (m0, p0, cm)
    | S steps' =>
      match map.get (getMem m) (getPc m) with
      | Some _ =>
        match its with
        | nil =>
          (* Instruction already exists, step... *)
          match mpstep (m,p), funSteps with
          | Some ((m',p'),_t,o), (S n)::ns =>
            (* ...and recurse. *)
            gen_exec_aux steps' (n::ns) i t m0 p0 m' p' cm f nextF its codeP dataP callP 
          | Some ((m',p'),_t,o), _ =>
            gen_exec_aux steps' funSteps i t m0 p0 m' p' cm f nextF its codeP dataP callP 
          | _, _ =>
            (*trace "Something went wrong."*) ret (m0,p0,cm)
          end
        | _ =>
          (*trace ("Existing instruction mid-sequence" ++ nl)%string*)
          ret (m0, p0, cm)
        end
      | _ =>
        (* Check if there is anything left to put *)
        (bindGen
           (match its with
            | [] =>
              (* Generate an instruction sequence. *)
              (* TODO: Sequences, calls. *)
              bindGen (genInstrSeq i t m p dataP codeP callP cm f nextF funSteps)
                      (fun '(itfas,funSteps') =>
                         match itfas with
                         | (i,t,f',a) :: itfs' =>
                           (*trace (show (i,t,f',a) ++ nl)%string*)
                           (returnGen (a, f', (i,t), itfs',funSteps'))
                         | _ => exception "EmptyInstrSeq"
                         end)
            | ((i,t,f',a)::itfs') =>
              match funSteps with
              | (S n)::rest =>
                returnGen (a, f', (i,t), itfs', (n::rest))
              | _ =>
                returnGen (a, f', (i,t), itfs', funSteps)
              end
            end)
           (fun '(a, f', (is,it), its, funSteps') =>
              let nextF' := if Nat.eqb f' nextF then
                              S nextF else nextF in
              let m0' := setInstrI (getPc m) m0 is in
              let m'  := setInstrI (getPc m) m  is in
              let p0' := setInstrTagI (word.unsigned (getPc m)) p0 it in
              let p'  := setInstrTagI (word.unsigned (getPc m)) p it in
              let cm' := map.put cm (word.unsigned (getPc m)) (Some a) in
              match mpstep (m', p') with
              | Some ((m'', p''), _t, o) =>
                (gen_exec_aux steps' funSteps' i t m0' p0' m'' p'' cm' f' nextF' its dataP codeP callP)
              | _ =>
                (*trace ("Couldn't step" ++ nl(* ++  printMachine m' p' cm' ++ nl*))%string*)
                      ret (m0', p0', cm')
              end))
      end
    end.

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
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    bindGen (genDataMemory i t m0 p0)
            (fun '(ms,ps) =>
               bindGen (genGPRs t ms ps)
                       (fun '(ms', ps') =>
                          (* Something about sp?
                             let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
                             ps' <- genGPRTs pplus ps (genGPRTag pplus)
                             let ps'' = ps' & pgpr . at sp ?~ spTag
                           *)
                          (gen_exec_aux maxFuel [funMaxFuel] i t ms' ps' ms' ps' cm0 O (S O)
                                        (initSeq O) dataP codeP callP))).

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
       ; pctags := [Tpc 0; Th2]
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
  let callP := fun tt => match tt with
                         | [Tinstr; Th1] => true
                         | _ => false
                         end in  
  genMachine defLayoutInfo defTagInfo zeroedRiscvMachine zeroedPolicyState map.empty
             dataP codeP callP.
End GenRISCVLazyFixed.*)

Module GenRISCVLazyOrig <: Gen RISCVLazyOrig RISCVDef.
  Import RISCVLazyOrig.
  Import TagPolicyLazyOrig.
  Import RISCVDef.
  Module PM := PM.
  Import PM.
  Import PrintRISCVLazyOrig.

  Definition maxFuel := 100%nat.
  Definition funMaxFuel := 10%nat.

  Definition r0 : Register := 0.
  Definition ra : Register := 1.
  Definition sp : Register := 2.
  
  (*- TODO: Sometimes we might want to use/target ra and sp to inject/find bugs? *)
  Definition minReg : Register := 8.
  Definition noRegs : nat := 3%nat.
  Definition maxReg : Register := minReg + Z.of_nat noRegs - 1.
  
  Record TagInfo :=
    { regTag  : TagSet
    ; codeTag : TagSet
    ; dataTag : TagSet 
    ; pcTag   : TagSet
    }.

  Definition defTagInfo :=
    {| regTag  := nil
     ; codeTag := [Tinstr]
     ; dataTag := nil                    
     ; pcTag   := [Tpc 0]
    |}.

  Record PtrInfo := { pID     : Register
                    ; pVal    : Z
                    ; pMinImm : Z
                    ; pMaxImm : Z
                    ; pTag : TagSet
                    }.

  Instance ShowPtrInfo : Show PtrInfo :=
    {| show p :=
         "{| " ++ "pID: " ++ show (pID p) ++ " ; "
               ++ "pVal: " ++ show (pVal p) ++ " ; "
               ++ "pMinImm: " ++ show (pMinImm p) ++ " ; "
               ++ "pMaxImm: " ++ show (pMaxImm p) ++ " ; "
               ++ "pTag: " ++ show (pTag p) ++ " |}"
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
        | O => []
        | S len' => start :: aux (start + 4) len'
        end in
    aux lo len.
    
  Definition setInstrI addr (mp : MachineState) (i : InstructionI) : MachineState :=
    let (m,p) := mp in
    let prog := [encode i] in
    let m' :=
      withXAddrs
      (addXAddrRange addr (4 * Datatypes.length prog)
                     (getXAddrs m))
      (withMem
         (unchecked_store_byte_list addr
                                    (Z32s_to_bytes prog) (getMem m)) m) in
    (m',p).

  Definition setInstrTagI addr (mp : MachineState) (t : TagSet) : MachineState :=
    let (m,p) := mp in
    (m, p <| memtags := map.put (memtags p) addr t |>).

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
             (mp : MachineState)
             (dataP codeP : TagSet -> bool)
    : RegInfo :=
    let (m,p) := mp in
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
    if (n >=? 0)
    then bindGen (choose (0, Z.div n 4))
                 (fun n' => ret (Z.mul 4 n'))
    else ret 0.

  Definition genTargetReg (m : MachineState) : G Register :=
    choose (minReg, maxReg).

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ].

  Definition if_true_n (b:bool) (n:nat) :=
    if b then n else O.
  
  Definition genStackbasedWrite (i : LayoutInfo) (mp : MachineState) : G InstructionI :=
    let spVal := projw mp (Reg SP) in
    bindGen (genSourceReg mp)
            (fun rs =>
               freq [ (10%nat, ret (Sw sp rs (-4)))
                    ; (10%nat, ret (Sw sp rs (-8)))
                    ; (if_true_n (512 <? (wtoz spVal)) 1%nat, ret (Sw sp rs (-12)))
                    ; (if_true_n (516 <? spVal) 2%nat, (ret (Sw sp rs (-16))))
                    ; (if_true_n (520 <? spVal) 2%nat, (ret (Sw sp rs (-20))))
                    ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                      (fun off => ret (Sw sp rs (- off))))
                    ; (1%nat, bindGen (choose (0, 600 - spVal))
                                      (fun off => ret (Sw sp rs off)))
            ]).

    Definition genStackbasedRead (i : LayoutInfo) (mp : MachineState) : G InstructionI :=
      let spVal := projw mp (Reg SP) in
      bindGen (genTargetReg mp)
              (fun rd =>
                 freq [ (10%nat, ret (Lw rd sp (-4)))
                      ; (10%nat, ret (Lw rd sp (-8)))
                      ; (if_true_n (512 <? spVal) 1%nat, ret (Lw rd sp (-12)))
                      ; (if_true_n (516 <? spVal) 2%nat, ret (Lw rd sp (-16)))
                      ; (if_true_n (520 <? spVal) 2%nat, ret (Lw rd sp (-20)))
                      ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                        (fun off => ret (Lw rd sp (- off))))
                      ; (1%nat, bindGen (choose (0, 600 - spVal))
                                        (fun off => ret (Lw rd sp off)))
              ]).

  (*
    -- TODO: This might need to be further generalized in the future
    genInstr :: PolicyPlus -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Instr_I -> Gen TagSet) -> Gen (Instr_I, TagSet)
   *)
  Definition genInstr (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (cm : CodeMap_Impl)
             (dataP codeP : TagSet -> bool) (f : FunID)
    : G (InstructionI * TagSet * FunID * Operations) :=
    let groups := groupRegisters i t m dataP codeP in
    let a := arith groups in
    let d := dataPtr groups in
    let c := codePtr groups in
    let l := loadPtr groups in
    (*  trace ("Grouped loads: " ++ show l ++ nl)%string *)
    let def_a := {| aID := 0 |} in
    let def_dp := {| pID := 0; pVal := 0;
                     pMinImm := 0; pMaxImm := 0;
                     pTag := dataTag t
                  |} in

      (*  trace (show (l, badPtr groups)%string) *)
    let onNonEmpty {A} (l : list A) n :=
        match l with
        | [] => O
        | _  => n
        end in
    let noops : Operations := [] in
    freq [ (onNonEmpty a 1%nat,
            bindGen (elems_ def_a a) (fun ai =>
            bindGen (genTargetReg m) (fun rd =>
            bindGen (genImm (dataHi i)) (fun imm =>
            let instr := Addi rd (aID ai) imm in
            ret (instr, [Tinstr], f, noops)))))
         ; (4%nat, bindGen (genStackbasedWrite i m)
                           (fun instr =>
                              (ret (instr, [Tinstr], f, noops))))
         ; (4%nat, bindGen (genStackbasedRead i m)
                           (fun instr =>
                              ret (instr, [Tinstr], f, noops)))
(*           ;  (3%nat, match map.get (getRegs m) sp with
                      | Some spVal' =>
                        let spVal := word.unsigned spVal' in
                        let minImm := spVal - stackLo i in
                        let maxImm := stackHi i - spVal in
                        bindGen (genImm (maxImm - minImm)) (fun imm' =>
                        let imm := minImm + imm' in
                        bindGen (genTargetReg m) (fun rd =>
                        let instr := Lw rd sp imm in
                        ret (instr, [Tinstr], f, normal)))

                      | _ => exception "No sp?"
                      end)*)
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
(*             ;  ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
                 bindGen (elems_ def_dp d) (fun pi =>
                 bindGen (genSourceReg m) (fun rs =>
                 bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
                 let imm := pMinImm pi + imm' in
                 let instr := Sw (pID pi) rs imm in
                 ret (instr, [Tinstr], f, normal))))) *)
           ;   (onNonEmpty a 1%nat,
                bindGen (elems_ def_a a) (fun ai1 =>
                bindGen (elems_ def_a a) (fun ai2 =>
                bindGen (genTargetReg m) (fun rd =>
                let instr := Add rd (aID ai1) (aID ai2) in
                ret (instr, [Tinstr], f, noops)))))
    ].

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

  (* FIXME Code annotations are replaced by operations, but only the constructor
     carries meaning! *)
  Definition callHead offset f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Jal ra offset, [Tinstr; Tcall], f, [(Call f [] [])])].

  Definition headerHead f:
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Sw sp ra 0, [Tinstr; Th1], f, [(*noops*)])].

  Definition initSeq f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [  (Addi sp sp 12 , [Tinstr; Th2], f, [(*noops*)])
(*       (Sw sp 8 (-8)  , [Tinstr]     , f, normal);
       (Sw sp 9 (-4)  , [Tinstr]     , f, normal)*)
    ].
  
  Definition callSeq offset f nextF :=
    callHead offset f ++ headerHead nextF ++ initSeq nextF.
  
  (* Based on Rob's 
     (* 08 *) IInstruction (Sw SP RA 0); (* H1 *)
     (* 12 *) IInstruction (Addi SP SP 12); (* H2 *)
   *)
  Definition genCall (l : LayoutInfo) (t : TagInfo)
             (mp : MachineState)
             (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
             (callP :  TagSet -> bool) :
    option (G (list (InstructionI * TagSet * FunID * Operations))) :=
    let (m,p) := mp in
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
                      callHead i f
                  | _ => exception ("genCall - nofid: " ++ show (word.unsigned (getPc m) + i) ++ nl)%string
                  end) existingSites  in
    let newOpts :=
      List.map (fun i => callSeq i f nextF) newCallSites in
    match exOpts ++ newOpts with
    | [] => None
    | x :: xs =>
        Some (elems_ x (x :: xs))
    end.
  
  Definition returnSeq (f : FunID) :=
    [ (Addi sp sp (-12) , [Tinstr; Tr1], f, [(*noops*)])
    ; (Lw   ra sp 0     , [Tinstr; Tr2], f, [(*noops*)])
    ; (Jalr ra ra 0     , [Tinstr; Tr3], f, [Return])
    ].

  Definition genRetSeq (m : MachineState) (cm : CodeMap_Impl) (f : FunID) :=
    let spv := projw m (Reg sp) in
    if (512 <? (wtoz spv))%Z 
    then Some (returnGen (returnSeq f))
    else None.

  Definition genInstrSeq
             (l : LayoutInfo) (t : TagInfo)
             (mp : MachineState)
             (dataP codeP callP : TagSet -> bool)
             (cm : CodeMap_Impl) (f nextF : FunID)
             (fSteps : list nat)
    : G (list (InstructionI * TagSet * FunID * Operations) * (list nat)) :=
    let fromInstr :=
        bindGen (genInstr l t mp cm dataP codeP f)
                (fun itf => returnGen ([itf])) in
    let '(fFuel, rest) :=
        match fSteps with
        | (S fFuel)::rest => (fFuel, rest)
        | O::rest => (O, rest)
        | _ => (O, [])
        end in
    let returnFreq := (funMaxFuel - fFuel)%nat in
    let instrFreq := (fFuel - 2)%nat in
    let callFreq := 1%nat in
    let instGen := bindGen fromInstr (fun g => ret (g,fFuel::rest)) in
    match genCall l t mp cm f nextF callP,
          genRetSeq mp cm f with
    | None, None => instGen
    | None, Some g2 =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest))) ])%nat
    | Some g1, None =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest))) ])%nat
    | Some g1, Some g2 =>
      freq_ instGen ([ (instrFreq, bindGen fromInstr (fun g => ret (g,fFuel::rest)))
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest)))
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest)))
                    ])%nat
    end.

  (* variantOf (fun k => fst c k = Sealed d) m n -> *)
  Definition genVariantOf (d : nat)
             (c : Ctx) (m : MachineState)
  : G MachineState :=
    foldGen (fun macc k =>
               (*trace (show ("Varying:", k, fst c k)) *)
               (match fst c k with
                | public =>
                  returnGen macc
                | _ =>
                  bindGen (genImm 40) (fun z =>
                                         (*               trace ("Trying to set: " ++ show k ++ " to " ++ show z ++ " which was " ++ show (fst c k) ++ nl ++ "Previous value was: " ++ show (proj macc k) ++ nl ++ " Next value will be: " ++ show (proj (jorp macc k z) k) ++ nl ++ nl)%string *)
                                         (returnGen (jorpw macc k z)))
                end)
            )
            (getElements m) m .

  Definition genVariantByList (ks : list Element) (m : MachineState) : G MachineState :=
    foldGen (fun macc k =>
               match List.find (fun k' => keqb k k') ks with
               | Some _ => bindGen (genImm 40) (fun z => returnGen (jorpw macc k z))
               | None => returnGen macc
               end)
          ks m.

  Instance ShowStuff : Show (InstructionI * TagSet * FunID * Operations) :=
    {| show '(i, ts, f, a) := (show i ++ "@" ++ show ts ++ "|" ++ show f)%string |}.
  
  (*
    -- | Generation by execution receives an initial machine X PIPE state and
    -- | generates instructions until n steps have been executed.
    -- | Returns the original machines with just the instruction memory locations
    -- | updated.
    genByExec :: PolicyPlus -> Int -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
    Gen (Machine_State, PIPE_State)
   *)
  Fixpoint gen_exec_aux (steps : nat)
           (funSteps : list nat)
           (i : LayoutInfo) (t : TagInfo)
           (mp0 : MachineState)
           (mp  : MachineState)
           (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
           (its : list (InstructionI * TagSet * FunID * Operations))
           (dataP codeP callP : TagSet -> bool)
    (* num calls? *)
    : G (MachineState * CodeMap_Impl) :=
    let '(m0,p0) := mp0 in
    let '(m,p) := mp in
    (*trace ("GenExec..." ++ show steps ++ " " ++ show its ++ printPC m p ++ nl)%string*)
    match steps with
    | O =>
      (* Out-of-fuel: End generation. *)
      ret (mp0, cm)
    | S steps' =>
      match map.get (getMem m) (getPc m) with
      | Some _ =>
        match its with
        | nil =>
          (* Instruction already exists, step... *)
          match mpstep (m,p), funSteps with
          | ((m',p'),_t,o), (S n)::ns =>
            (* ...and recurse. *)
            gen_exec_aux steps' (n::ns) i t mp0 (m',p') cm f nextF its codeP dataP callP 
          | ((m',p'),_t,o), _ =>
            gen_exec_aux steps' funSteps i t mp0 (m',p') cm f nextF its codeP dataP callP 
          end
        | _ =>
          (*trace ("Existing instruction mid-sequence" ++ nl)%string*)
          ret (m0, p0, cm)
        end
      | _ =>
        (* Check if there is anything left to put *)
        (bindGen
           (match its with
            | [] =>
              (* Generate an instruction sequence. *)
              (* TODO: Sequences, calls. *)
              bindGen (genInstrSeq i t mp dataP codeP callP cm f nextF funSteps)
                      (fun '(itfas,funSteps') =>
                         match itfas with
                         | (i,t,f',a) :: itfs' =>
                           (*trace (show (i,t,f',a) ++ nl)%string*)
                           (returnGen (a, f', (i,t), itfs',funSteps'))
                         | _ => exception "EmptyInstrSeq"
                         end)
            | ((i,t,f',a)::itfs') =>
              match funSteps with
              | (S n)::rest =>
                returnGen (a, f', (i,t), itfs', (n::rest))
              | _ =>
                returnGen (a, f', (i,t), itfs', funSteps)
              end
            end)
           (fun '(a, f', (is,it), its, funSteps') =>
              let nextF' := if Nat.eqb f' nextF then
                              S nextF else nextF in
              let mp0' := setInstrI (getPc m) mp0 is in
              let mp'  := setInstrI (getPc m) mp  is in
              let mp0'' := setInstrTagI (word.unsigned (getPc m)) mp0' it in
              let mp''  := setInstrTagI (word.unsigned (getPc m)) mp' it in
              let cm' := map.put cm (word.unsigned (getPc m)) (Some a) in
              match mpstep mp'' with
              | (mp''', _t, o) =>
                (gen_exec_aux steps' funSteps' i t mp0'' mp''' cm' f' nextF' its dataP codeP callP)
              end))
      end
    end.

  Definition replicateGen {A} (n : nat) (g : G A) : G (list A) :=
    let fix aux n :=
        match n with
        | O => returnGen nil
        | S n' => liftGen2 cons g (aux n')
        end in
    aux n.
  
  Definition genGPRs (t : TagInfo)
             (mp : MachineState)
    : G MachineState :=
    let (m,p) := mp in
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
             (mp : MachineState)
    : G MachineState :=
    let (m,p) := mp in
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
             (mp0 : MachineState)
             (cm0 : CodeMap_Impl)
             (dataP codeP callP : TagSet -> bool)
    : G (MachineState * CodeMap_Impl) :=
    bindGen (genDataMemory i t mp0)
            (fun '(mps) =>
               bindGen (genGPRs t mps)
                       (fun mps' =>
                          (* Something about sp?
                             let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
                             ps' <- genGPRTs pplus ps (genGPRTag pplus)
                             let ps'' = ps' & pgpr . at sp ?~ spTag
                           *)
                          (gen_exec_aux maxFuel [funMaxFuel] i t mps' mps' cm0 O (S O)
                                        (initSeq O) dataP codeP callP))).

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
       ; pctags := [Tpc 0; Th2]
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
  let callP := fun tt => match tt with
                         | [Tinstr; Th1] => true
                         | _ => false
                         end in  
  genMachine defLayoutInfo defTagInfo (zeroedRiscvMachine,zeroedPolicyState) map.empty
             dataP codeP callP.

(* To encode specific examples, the relevant bits already exist as part of
   zeroedRiscvMachine. zeroedPolicyState, gen_exec_aux, etc. Consider a
   rather verbose encoding of a fixed counterexample: *)

  Definition setRegs (rvals : list (Z * Z)) (mp : MachineState) : MachineState :=
    let (m, p) := mp in
    let rvals' := seq.map (fun '(i, v) => (i, word.of_Z v)) rvals in
    (m <| getRegs := map.putmany_of_list rvals' (getRegs m) |>, p).

  Definition setInstrs (instrs : list (Z * InstructionI)) (mp : MachineState) : MachineState :=
    List.fold_right (fun '(a, i) m => setInstrI (word.of_Z a) m i) mp instrs.

  Definition setMemTags (mtags : list (Z * TagSet)) (mp : MachineState) : MachineState :=
    let (m, p) := mp in
    (m, p <| memtags := map.putmany_of_list mtags (memtags p) |>).

  Definition setRegTags (rtags : list (Z * TagSet)) (mp : MachineState) : MachineState :=
    let (m, p) := mp in
    (m, p <| regtags := map.putmany_of_list rtags (regtags p) |>).

  Definition ex_gen
    (mem : list (Z * InstructionI * TagSet * option Operations))
    (regs : list (Z * Z * TagSet)) :
    G (MachineState * CodeMap_Impl) :=
    (* Machine state components from example description *)
    let ait := seq.unzip1 mem in
    let ai := seq.unzip1 ait in
    let addrs := seq.unzip1 ai in
    let instrs := seq.zip addrs (seq.unzip2 ai) in
    let mtags := seq.zip addrs (seq.unzip2 ait) in
    let ops := seq.zip addrs (seq.unzip2 mem) in
    let rv := seq.unzip1 regs in
    let rids := seq.unzip1 rv in
    let rvals := seq.zip rids (seq.unzip2 rv) in
    let rtags := seq.zip rids (seq.unzip2 regs) in
    (* Machine state, code map and generator *)
    let ms := setRegs rvals (
              setInstrs instrs (
              setRegTags rtags (
              setMemTags mtags
              (zeroedRiscvMachine, zeroedPolicyState)))) in
    let cm := map.putmany_of_list ops map.empty in
    returnGen (ms, cm).

(*
PC:0 @ Tpc 0Th2
Registers:
0 : 0 @
1 : 0 @
2 : 500 @ Tsp
8 : 12 @
9 : 0 @
10 : 4 @
Memory:
0 : Addi 2 2 12 @ TinstrTh2 < Some [] > - public
4 : Sw 2 0 -8 @ Tinstr < Some [] > - public
8 : Jal 1 60 @ TinstrTcall < Some [Call] > - public
68 : Sw 2 1 0 @ TinstrTh1 < Some [] > - public
72 : Addi 2 2 12 @ TinstrTh2 < Some [] > - public
76 : Sw 2 10 -8 @ Tinstr < Some [] > - public
80 : Lw 10 2 -4 @ Tinstr < Some [] > - public
500 : 0 @Tstack 0 < None > - free
1000 : 636 @ < None > - public
1004 : 420 @ < None > - public
1008 : 1016 @ < None > - public
1012 : 916 @ < None > - public
1016 : 192 @ < None > - public
*)

  (* Counterexample to prop_laziestIntegrity', use this generator instead of the
     random machine execution generator to reproduce *)
  Definition cex01 : G (MachineState * CodeMap_Impl) :=
    ex_gen
      [(  0, Addi 2 2 12,  [Tinstr; Th2],   Some [] );
       (  4, Sw 2 0 (-8),  [Tinstr],        Some [] );
       (  8, Jal 1 60,     [Tinstr; Tcall], Some [(Call O [] [])] );
       ( 68, Sw 2 1 0,     [Tinstr; Th1],   Some [] );
       ( 72, Addi 2 2 12,  [Tinstr; Th2],   Some [] );
       ( 76, Sw 2 10 (-8), [Tinstr],        Some [] );
       ( 80, Lw 10 2 (-4), [Tinstr],        Some [] )]
      [(  8, 12, [] );
       (  9,  0, [] );
       ( 10,  4, [] )].

  Definition cex02 : G (MachineState * CodeMap_Impl) :=

    (* Machine state *)
    let ms : MachineState :=
      let rs0 :=
        {|
          getRegs :=
            List.fold_right
              (fun '(i, v) m => map.put m i (word.of_Z v))
              map.empty
              [
                (0, 0);
                (1, 0);
                (2, 500);
                (8, 12);
                (9, 0);
                (10, 4)
              ];
          getPc := ZToReg 0;
          getNextPc := ZToReg 4;
          getMem :=
            unchecked_store_byte_list
              (word.of_Z 500)
              (Z32s_to_bytes (repeat 0 125))
              map.empty;
          getXAddrs := [];
          getLog := []
        |}
      in
      let ps0 :=
        {|
          nextid := 0;
          pctags := [Tpc 0; Th2];
          regtags :=
            map.putmany_of_list
              [
                (0, []);
                (1, []);
                (2, [Tsp]);
                (8, []);
                (9, []);
                (10, [])
              ]
              map.empty;
          memtags :=
            map.putmany_of_list
              [
                (0, [Tinstr; Th2]);
                (4, [Tinstr]);
                (8, [Tinstr; Tcall]);
                (12, [Tinstr]);
                (16, [Tinstr; Tcall]);
                (100, [Tinstr; Th1]);
                (104, [Tinstr; Th2]);
                (108, [Tinstr]);
                (112, [Tinstr]);
                (116, [Tinstr]); (* machine gets stuck here (2nd pass) *)
                (120, [Tinstr]);
                (124, [Tinstr; Tr1]);
                (128, [Tinstr; Tr2]);
                (132, [Tinstr; Tr3]);
                (500, [Tstack 0])
                (* (1000, []); *)
                (* (1004, []); *)
                (* (1008, []); *)
                (* (1012, []); *)
                (* (1016, []) *)
              ]
              (snd (List.fold_right (fun x '(i,m) => (i+4, map.put m i x)) (500, map.empty)
                                    (repeat nil 125)))
        |}
      in
      let ms0 := (rs0, ps0) in
      let instrs :=
        [
          (* main *)
          (0, Addi 2 2 12);
          (4, Addi 10 0 1);
          (8, Jal 1 92);
          (12, Addi 10 0 0);
          (16, Jal 1 84);
          (* f *)
          (100, Sw 2 1 0); (* header *)
          (104, Addi 2 2 12);
          (108, Beq 10 0 8); (* check flag *)
          (112, Sw 2 8 (-4)); (* then: init *)
          (116, Lw 8 2 (-4)); (* else: reuse *)
          (120, Sw 2 8 (-8));
          (124, Addi 2 2 (-12)); (* footer *)
          (128, Lw 1 2 0);
          (132, Jalr 1 1 0)
        ]
      in
      List.fold_right (fun '(a, i) m => setInstrI (word.of_Z a) m i) ms0 instrs
    in

    (* Code map *)
    let cm : CodeMap_Impl :=
      map.putmany_of_list
        [
          (0, Some []);
          (4, Some []);
          (8, Some [(Call O [] [])]);
          (12, Some []);
          (16, Some [(Call O [] [])]);
          (100, Some []);
          (104, Some []);
          (108, Some []);
          (112, Some []);
          (116, Some []);
          (120, Some []);
          (124, Some []);
          (128, Some []);
          (132, Some [Return])
        ]
        map.empty
    in

    (* Generator *)
    returnGen (ms, cm).
End GenRISCVLazyOrig.

(*Module GenRISCVLazyNoCheck <: Gen RISCVObs TPLazyNoCheck DLObs TSSRiscvDefault.
  Module MPC := TestMPC RISCVObs TPLazyNoCheck DLObs TSSRiscvDefault.
  Import MPC.
  Import PrintRISCVLazyNoCheck.

  Definition maxFuel := 100%nat.
  Definition funMaxFuel := 10%nat.

  Definition r0 : Register := 0.
  Definition ra : Register := 1.
  Definition sp : Register := 2.
  
  (*- TODO: Sometimes we might want to use/target ra and sp to inject/find bugs? *)
  Definition minReg : Register := 8.
  Definition noRegs : nat := 3%nat.
  Definition maxReg : Register := minReg + Z.of_nat noRegs - 1.
  
  Record TagInfo :=
    { regTag  : TagSet
    ; codeTag : TagSet
    ; dataTag : TagSet 
    ; pcTag   : TagSet
    }.

  Definition defTagInfo :=
    {| regTag  := nil
     ; codeTag := [Tinstr]
     ; dataTag := nil                    
     ; pcTag   := [Tpc 0]
    |}.

  Record PtrInfo := { pID     : Register
                    ; pVal    : Z
                    ; pMinImm : Z
                    ; pMaxImm : Z
                    ; pTag : TagSet
                    }.

  Instance ShowPtrInfo : Show PtrInfo :=
    {| show p :=
         "{| " ++ "pID: " ++ show (pID p) ++ " ; "
               ++ "pVal: " ++ show (pVal p) ++ " ; "
               ++ "pMinImm: " ++ show (pMinImm p) ++ " ; "
               ++ "pMaxImm: " ++ show (pMaxImm p) ++ " ; "
               ++ "pTag: " ++ show (pTag p) ++ " |}"
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
        | O => []
        | S len' => start :: aux (start + 4) len'
        end in
    aux lo len.
    
  Definition setInstrI addr (m : MachineState) (i : InstructionI) : MachineState :=
    let prog := [encode i] in
    withXAddrs
      (addXAddrRange addr (4 * Datatypes.length prog)
                     (getXAddrs m))
      (withMem
         (unchecked_store_byte_list addr
                                    (Z32s_to_bytes prog) (getMem m)) m).

  Definition setInstrTagI addr (p : PolicyState) (t : TagSet) : PolicyState :=
    p <| memtags := map.put (memtags p) addr t |>.

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
    if (n >=? 0)
    then bindGen (choose (0, Z.div n 4))
                 (fun n' => ret (Z.mul 4 n'))
    else ret 0.

  Definition genTargetReg (m : MachineState) : G Register :=
    choose (minReg, maxReg).

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ].

  Definition if_true_n (b:bool) (n:nat) :=
    if b then n else O.
  
  Definition genStackbasedWrite (i : LayoutInfo) (m : MachineState) : G InstructionI :=
    let spVal := projw m (Reg SP) in
    bindGen (genSourceReg m)
            (fun rs =>
               freq [ (10%nat, ret (Sw sp rs (-4)))
                    ; (10%nat, ret (Sw sp rs (-8)))
                    ; (if_true_n (512 <? spVal) 1%nat, ret (Sw sp rs (-12)))
                    ; (if_true_n (516 <? spVal) 2%nat, (ret (Sw sp rs (-16))))
                    ; (if_true_n (520 <? spVal) 2%nat, (ret (Sw sp rs (-20))))
                    ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                     (fun off => ret (Sw sp rs (- off))))
                    ; (1%nat, bindGen (choose (0, 600 - spVal))
                                      (fun off => ret (Sw sp rs off)))
            ]).

    Definition genStackbasedRead (i : LayoutInfo) (m : MachineState) : G InstructionI :=
      let spVal := projw m (Reg SP) in
      bindGen (genTargetReg m)
              (fun rd =>
                 freq [ (10%nat, ret (Lw rd sp (-4)))
                      ; (10%nat, ret (Lw rd sp (-8)))
                      ; (if_true_n (512 <? spVal) 1%nat, ret (Lw rd sp (-12)))
                      ; (if_true_n (516 <? spVal) 2%nat, ret (Lw rd sp (-16)))
                      ; (if_true_n (520 <? spVal) 2%nat, ret (Lw rd sp (-20)))
                      ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                        (fun off => ret (Lw rd sp (- off))))
                      ; (1%nat, bindGen (choose (0, 600 - spVal))
                                        (fun off => ret (Lw rd sp off)))
              ]).

  (*
    -- TODO: This might need to be further generalized in the future
    genInstr :: PolicyPlus -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Instr_I -> Gen TagSet) -> Gen (Instr_I, TagSet)
   *)
  Definition genInstr (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl)
             (dataP codeP : TagSet -> bool) (f : FunID)
    : G (InstructionI * TagSet * FunID * Operations) :=
    let groups := groupRegisters i t m p dataP codeP in
    let a := arith groups in
    let d := dataPtr groups in
    let c := codePtr groups in
    let l := loadPtr groups in
    (*  trace ("Grouped loads: " ++ show l ++ nl)%string *)
    let def_a := {| aID := 0 |} in
    let def_dp := {| pID := 0; pVal := 0;
                     pMinImm := 0; pMaxImm := 0;
                     pTag := dataTag t
                  |} in

      (*  trace (show (l, badPtr groups)%string) *)
    let onNonEmpty {A} (l : list A) n :=
        match l with
        | [] => O
        | _  => n
        end in
    let noops : Operations := [] in
    freq [ (onNonEmpty a 1%nat,
            bindGen (elems_ def_a a) (fun ai =>
            bindGen (genTargetReg m) (fun rd =>
            bindGen (genImm (dataHi i)) (fun imm =>
            let instr := Addi rd (aID ai) imm in
            ret (instr, [Tinstr], f, noops)))))
         ; (4%nat, bindGen (genStackbasedWrite i m)
                           (fun instr =>
                              (ret (instr, [Tinstr], f, noops))))
         ; (4%nat, bindGen (genStackbasedRead i m)
                           (fun instr =>
                              ret (instr, [Tinstr], f, noops)))
(*           ;  (3%nat, match map.get (getRegs m) sp with
                      | Some spVal' =>
                        let spVal := word.unsigned spVal' in
                        let minImm := spVal - stackLo i in
                        let maxImm := stackHi i - spVal in
                        bindGen (genImm (maxImm - minImm)) (fun imm' =>
                        let imm := minImm + imm' in
                        bindGen (genTargetReg m) (fun rd =>
                        let instr := Lw rd sp imm in
                        ret (instr, [Tinstr], f, normal)))

                      | _ => exception "No sp?"
                      end)*)
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
(*             ;  ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
                 bindGen (elems_ def_dp d) (fun pi =>
                 bindGen (genSourceReg m) (fun rs =>
                 bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
                 let imm := pMinImm pi + imm' in
                 let instr := Sw (pID pi) rs imm in
                 ret (instr, [Tinstr], f, normal))))) *)
           ;   (onNonEmpty a 1%nat,
                bindGen (elems_ def_a a) (fun ai1 =>
                bindGen (elems_ def_a a) (fun ai2 =>
                bindGen (genTargetReg m) (fun rd =>
                let instr := Add rd (aID ai1) (aID ai2) in
                ret (instr, [Tinstr], f, noops)))))
    ].

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

  (* FIXME Code annotations are replaced by operations, but only the constructor
     carries meaning! *)
  Definition callHead offset f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Jal ra offset, [Tinstr; Tcall], f, [(Call f [] [])])].

  Definition headerHead f:
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Sw sp ra 0, [Tinstr; Th1], f, [(*noops*)])].

  Definition initSeq f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [  (Addi sp sp 12 , [Tinstr; Th2], f, [(*noops*)])
(*       (Sw sp 8 (-8)  , [Tinstr]     , f, normal);
       (Sw sp 9 (-4)  , [Tinstr]     , f, normal)*)
    ].
  
  Definition callSeq offset f nextF :=
    callHead offset f ++ headerHead nextF ++ initSeq nextF.
  
  (* Based on Rob's 
     (* 08 *) IInstruction (Sw SP RA 0); (* H1 *)
     (* 12 *) IInstruction (Addi SP SP 12); (* H2 *)
   *)
  Definition genCall (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
             (callP :  TagSet -> bool) :
    option (G (list (InstructionI * TagSet * FunID * Operations)))
    :=
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
                        callHead i f
                      | _ => exception ("genCall - nofid: " ++ show (word.unsigned (getPc m) + i) ++ nl)%string
                      end) existingSites  in
      let newOpts :=
          List.map (fun i => callSeq i f nextF) newCallSites in
      match exOpts ++ newOpts with
      | [] => None
      | x :: xs =>
        Some (elems_ x (x :: xs))
      end.
  
  Definition returnSeq (f : FunID) :=
    [ (Addi sp sp (-12) , [Tinstr; Tr1], f, [(*noops*)])
    ; (Lw   ra sp 0     , [Tinstr; Tr2], f, [(*noops*)])
    ; (Jalr ra ra 0     , [Tinstr; Tr3], f, [Return])
    ].

  Definition genRetSeq (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (f : FunID) :=
    let spv := projw m (Reg sp) in
    if (512 <? spv)%Z 
    then Some (returnGen (returnSeq f))
    else None.

  Definition genInstrSeq
             (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (dataP codeP callP : TagSet -> bool)
             (cm : CodeMap_Impl) (f nextF : FunID)
             (fSteps : list nat)
    : G (list (InstructionI * TagSet * FunID * Operations) * (list nat)) :=
    let fromInstr :=
        bindGen (genInstr l t m p cm dataP codeP f)
                (fun itf => returnGen ([itf])) in
    let '(fFuel, rest) :=
        match fSteps with
        | (S fFuel)::rest => (fFuel, rest)
        | O::rest => (O, rest)
        | _ => (O, [])
        end in
    let returnFreq := (funMaxFuel - fFuel)%nat in
    let instrFreq := (fFuel - 2)%nat in
    let callFreq := 1%nat in
    let instGen := bindGen fromInstr (fun g => ret (g,fFuel::rest)) in
    match genCall l t m p cm f nextF callP,
          genRetSeq m p cm f with
    | None, None => instGen
    | None, Some g2 =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest))) ])%nat
    | Some g1, None =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest))) ])%nat
    | Some g1, Some g2 =>
      freq_ instGen ([ (instrFreq, bindGen fromInstr (fun g => ret (g,fFuel::rest)))
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest)))
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest)))
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
                                         (*               trace ("Trying to set: " ++ show k ++ " to " ++ show z ++ " which was " ++ show (fst c k) ++ nl ++ "Previous value was: " ++ show (proj macc k) ++ nl ++ " Next value will be: " ++ show (proj (jorp macc k z) k) ++ nl ++ nl)%string *)
                                         (returnGen (jorp macc k z)))
                end)
            )
            (getElements m) m .

  Definition genVariantByList (ks : list Element) (m : MachineState) : G MachineState :=
    foldGen (fun macc k =>
               match List.find (fun k' => keqb k k') ks with
               | Some _ => bindGen (genImm 40) (fun z => returnGen (jorp macc k z))
               | None => returnGen macc
               end)
          ks m.

  Instance ShowStuff : Show (InstructionI * TagSet * FunID * Operations) :=
    {| show '(i, ts, f, a) := (show i ++ "@" ++ show ts ++ "|" ++ show f)%string |}.
  
  (*
    -- | Generation by execution receives an initial machine X PIPE state and
    -- | generates instructions until n steps have been executed.
    -- | Returns the original machines with just the instruction memory locations
    -- | updated.
    genByExec :: PolicyPlus -> Int -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
    Gen (Machine_State, PIPE_State)
   *)
  Fixpoint gen_exec_aux (steps : nat)
           (funSteps : list nat)
           (i : LayoutInfo) (t : TagInfo)
           (m0 : MachineState) (p0 : PolicyState)
           (m  : MachineState) (p  : PolicyState)
           (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
           (its : list (InstructionI * TagSet * FunID * Operations))
           (dataP codeP callP : TagSet -> bool)
    (* num calls? *)
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    (*trace ("GenExec..." ++ show steps ++ " " ++ show its ++ printPC m p ++ nl)%string*)
    match steps with
    | O =>
      (* Out-of-fuel: End generation. *)
      ret (m0, p0, cm)
    | S steps' =>
      match map.get (getMem m) (getPc m) with
      | Some _ =>
        match its with
        | nil =>
          (* Instruction already exists, step... *)
          match mpstep (m,p), funSteps with
          | Some ((m',p'),_t,o), (S n)::ns =>
            (* ...and recurse. *)
            gen_exec_aux steps' (n::ns) i t m0 p0 m' p' cm f nextF its codeP dataP callP 
          | Some ((m',p'),_t,o), _ =>
            gen_exec_aux steps' funSteps i t m0 p0 m' p' cm f nextF its codeP dataP callP 
          | _, _ =>
            (*trace "Something went wrong."*) ret (m0,p0,cm)
          end
        | _ =>
          (*trace ("Existing instruction mid-sequence" ++ nl)%string*)
          ret (m0, p0, cm)
        end
      | _ =>
        (* Check if there is anything left to put *)
        (bindGen
           (match its with
            | [] =>
              (* Generate an instruction sequence. *)
              (* TODO: Sequences, calls. *)
              bindGen (genInstrSeq i t m p dataP codeP callP cm f nextF funSteps)
                      (fun '(itfas,funSteps') =>
                         match itfas with
                         | (i,t,f',a) :: itfs' =>
                           (*trace (show (i,t,f',a) ++ nl)%string*)
                           (returnGen (a, f', (i,t), itfs',funSteps'))
                         | _ => exception "EmptyInstrSeq"
                         end)
            | ((i,t,f',a)::itfs') =>
              match funSteps with
              | (S n)::rest =>
                returnGen (a, f', (i,t), itfs', (n::rest))
              | _ =>
                returnGen (a, f', (i,t), itfs', funSteps)
              end
            end)
           (fun '(a, f', (is,it), its, funSteps') =>
              let nextF' := if Nat.eqb f' nextF then
                              S nextF else nextF in
              let m0' := setInstrI (getPc m) m0 is in
              let m'  := setInstrI (getPc m) m  is in
              let p0' := setInstrTagI (word.unsigned (getPc m)) p0 it in
              let p'  := setInstrTagI (word.unsigned (getPc m)) p it in
              let cm' := map.put cm (word.unsigned (getPc m)) (Some a) in
              match mpstep (m', p') with
              | Some ((m'', p''), _t, o) =>
                (gen_exec_aux steps' funSteps' i t m0' p0' m'' p'' cm' f' nextF' its dataP codeP callP)
              | _ =>
                (*trace ("Couldn't step" ++ nl(* ++  printMachine m' p' cm' ++ nl*))%string*)
                      ret (m0', p0', cm')
              end))
      end
    end.

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
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    bindGen (genDataMemory i t m0 p0)
            (fun '(ms,ps) =>
               bindGen (genGPRs t ms ps)
                       (fun '(ms', ps') =>
                          (* Something about sp?
                             let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
                             ps' <- genGPRTs pplus ps (genGPRTag pplus)
                             let ps'' = ps' & pgpr . at sp ?~ spTag
                           *)
                          (gen_exec_aux maxFuel [funMaxFuel] i t ms' ps' ms' ps' cm0 O (S O)
                                        (initSeq O) dataP codeP callP))).

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
       ; pctags := [Tpc 0; Th2]
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
  let callP := fun tt => match tt with
                         | [Tinstr; Th1] => true
                         | _ => false
                         end in  
  genMachine defLayoutInfo defTagInfo zeroedRiscvMachine zeroedPolicyState map.empty
             dataP codeP callP.
End GenRISCVLazyNoCheck.

Module GenRISCVLazyNoDepth <: Gen RISCVObs TPLazyNoDepth DLObs TSSRiscvDefault.
  Module MPC := TestMPC RISCVObs TPLazyNoDepth DLObs TSSRiscvDefault.
  Import MPC.
  Import PrintRISCVLazyNoDepth.

  Definition maxFuel := 100%nat.
  Definition funMaxFuel := 10%nat.

  Definition r0 : Register := 0.
  Definition ra : Register := 1.
  Definition sp : Register := 2.
  
  (*- TODO: Sometimes we might want to use/target ra and sp to inject/find bugs? *)
  Definition minReg : Register := 8.
  Definition noRegs : nat := 3%nat.
  Definition maxReg : Register := minReg + Z.of_nat noRegs - 1.
  
  Record TagInfo :=
    { regTag  : TagSet
    ; codeTag : TagSet
    ; dataTag : TagSet 
    ; pcTag   : TagSet
    }.

  Definition defTagInfo :=
    {| regTag  := nil
     ; codeTag := [Tinstr]
     ; dataTag := nil                    
     ; pcTag   := [Tpc 0]
    |}.

  Record PtrInfo := { pID     : Register
                    ; pVal    : Z
                    ; pMinImm : Z
                    ; pMaxImm : Z
                    ; pTag : TagSet
                    }.

  Instance ShowPtrInfo : Show PtrInfo :=
    {| show p :=
         "{| " ++ "pID: " ++ show (pID p) ++ " ; "
               ++ "pVal: " ++ show (pVal p) ++ " ; "
               ++ "pMinImm: " ++ show (pMinImm p) ++ " ; "
               ++ "pMaxImm: " ++ show (pMaxImm p) ++ " ; "
               ++ "pTag: " ++ show (pTag p) ++ " |}"
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
        | O => []
        | S len' => start :: aux (start + 4) len'
        end in
    aux lo len.
    
  Definition setInstrI addr (m : MachineState) (i : InstructionI) : MachineState :=
    let prog := [encode i] in
    withXAddrs
      (addXAddrRange addr (4 * Datatypes.length prog)
                     (getXAddrs m))
      (withMem
         (unchecked_store_byte_list addr
                                    (Z32s_to_bytes prog) (getMem m)) m).

  Definition setInstrTagI addr (p : PolicyState) (t : TagSet) : PolicyState :=
    p <| memtags := map.put (memtags p) addr t |>.

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
    if (n >=? 0)
    then bindGen (choose (0, Z.div n 4))
                 (fun n' => ret (Z.mul 4 n'))
    else ret 0.

  Definition genTargetReg (m : MachineState) : G Register :=
    choose (minReg, maxReg).

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ].

  Definition if_true_n (b:bool) (n:nat) :=
    if b then n else O.
  
  Definition genStackbasedWrite (i : LayoutInfo) (m : MachineState) : G InstructionI :=
    let spVal := projw m (Reg SP) in
    bindGen (genSourceReg m)
            (fun rs =>
               freq [ (10%nat, ret (Sw sp rs (-4)))
                    ; (10%nat, ret (Sw sp rs (-8)))
                    ; (if_true_n (512 <? spVal) 1%nat, ret (Sw sp rs (-12)))
                    ; (if_true_n (516 <? spVal) 2%nat, (ret (Sw sp rs (-16))))
                    ; (if_true_n (520 <? spVal) 2%nat, (ret (Sw sp rs (-20))))
                    ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                     (fun off => ret (Sw sp rs (- off))))
                    ; (1%nat, bindGen (choose (0, 600 - spVal))
                                      (fun off => ret (Sw sp rs off)))
            ]).

    Definition genStackbasedRead (i : LayoutInfo) (m : MachineState) : G InstructionI :=
      let spVal := projw m (Reg SP) in
      bindGen (genTargetReg m)
              (fun rd =>
                 freq [ (10%nat, ret (Lw rd sp (-4)))
                      ; (10%nat, ret (Lw rd sp (-8)))
                      ; (if_true_n (512 <? spVal) 1%nat, ret (Lw rd sp (-12)))
                      ; (if_true_n (516 <? spVal) 2%nat, ret (Lw rd sp (-16)))
                      ; (if_true_n (520 <? spVal) 2%nat, ret (Lw rd sp (-20)))
                      ; (1%nat, bindGen (choose (spVal - 500, spVal))
                                        (fun off => ret (Lw rd sp (- off))))
                      ; (1%nat, bindGen (choose (0, 600 - spVal))
                                        (fun off => ret (Lw rd sp off)))
              ]).

  (*
    -- TODO: This might need to be further generalized in the future
    genInstr :: PolicyPlus -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Instr_I -> Gen TagSet) -> Gen (Instr_I, TagSet)
   *)
  Definition genInstr (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl)
             (dataP codeP : TagSet -> bool) (f : FunID)
    : G (InstructionI * TagSet * FunID * Operations) :=
    let groups := groupRegisters i t m p dataP codeP in
    let a := arith groups in
    let d := dataPtr groups in
    let c := codePtr groups in
    let l := loadPtr groups in
    (*  trace ("Grouped loads: " ++ show l ++ nl)%string *)
    let def_a := {| aID := 0 |} in
    let def_dp := {| pID := 0; pVal := 0;
                     pMinImm := 0; pMaxImm := 0;
                     pTag := dataTag t
                  |} in

      (*  trace (show (l, badPtr groups)%string) *)
    let onNonEmpty {A} (l : list A) n :=
        match l with
        | [] => O
        | _  => n
        end in
    let noops : Operations := [] in
    freq [ (onNonEmpty a 1%nat,
            bindGen (elems_ def_a a) (fun ai =>
            bindGen (genTargetReg m) (fun rd =>
            bindGen (genImm (dataHi i)) (fun imm =>
            let instr := Addi rd (aID ai) imm in
            ret (instr, [Tinstr], f, noops)))))
         ; (4%nat, bindGen (genStackbasedWrite i m)
                           (fun instr =>
                              (ret (instr, [Tinstr], f, noops))))
         ; (4%nat, bindGen (genStackbasedRead i m)
                           (fun instr =>
                              ret (instr, [Tinstr], f, noops)))
(*           ;  (3%nat, match map.get (getRegs m) sp with
                      | Some spVal' =>
                        let spVal := word.unsigned spVal' in
                        let minImm := spVal - stackLo i in
                        let maxImm := stackHi i - spVal in
                        bindGen (genImm (maxImm - minImm)) (fun imm' =>
                        let imm := minImm + imm' in
                        bindGen (genTargetReg m) (fun rd =>
                        let instr := Lw rd sp imm in
                        ret (instr, [Tinstr], f, normal)))

                      | _ => exception "No sp?"
                      end)*)
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
(*             ;  ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
                 bindGen (elems_ def_dp d) (fun pi =>
                 bindGen (genSourceReg m) (fun rs =>
                 bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
                 let imm := pMinImm pi + imm' in
                 let instr := Sw (pID pi) rs imm in
                 ret (instr, [Tinstr], f, normal))))) *)
           ;   (onNonEmpty a 1%nat,
                bindGen (elems_ def_a a) (fun ai1 =>
                bindGen (elems_ def_a a) (fun ai2 =>
                bindGen (genTargetReg m) (fun rd =>
                let instr := Add rd (aID ai1) (aID ai2) in
                ret (instr, [Tinstr], f, noops)))))
    ].

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

  (* FIXME Code annotations are replaced by operations, but only the constructor
     carries meaning! *)
  Definition callHead offset f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Jal ra offset, [Tinstr; Tcall], f, [(Call f [] [])])].

  Definition headerHead f:
    list (InstructionI * TagSet * FunID * Operations) :=
    [(Sw sp ra 0, [Tinstr; Th1], f, [(*noops*)])].

  Definition initSeq f :
    list (InstructionI * TagSet * FunID * Operations) :=
    [  (Addi sp sp 12 , [Tinstr; Th2], f, [(*noops*)])
(*       (Sw sp 8 (-8)  , [Tinstr]     , f, normal);
       (Sw sp 9 (-4)  , [Tinstr]     , f, normal)*)
    ].
  
  Definition callSeq offset f nextF :=
    callHead offset f ++ headerHead nextF ++ initSeq nextF.
  
  (* Based on Rob's 
     (* 08 *) IInstruction (Sw SP RA 0); (* H1 *)
     (* 12 *) IInstruction (Addi SP SP 12); (* H2 *)
   *)
  Definition genCall (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
             (callP :  TagSet -> bool) :
    option (G (list (InstructionI * TagSet * FunID * Operations)))
    :=
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
                        callHead i f
                      | _ => exception ("genCall - nofid: " ++ show (word.unsigned (getPc m) + i) ++ nl)%string
                      end) existingSites  in
      let newOpts :=
          List.map (fun i => callSeq i f nextF) newCallSites in
      match exOpts ++ newOpts with
      | [] => None
      | x :: xs =>
        Some (elems_ x (x :: xs))
      end.
  
  Definition returnSeq (f : FunID) :=
    [ (Addi sp sp (-12) , [Tinstr; Tr1], f, [(*noops*)])
    ; (Lw   ra sp 0     , [Tinstr; Tr2], f, [(*noops*)])
    ; (Jalr ra ra 0     , [Tinstr; Tr3], f, [Return])
    ].

  Definition genRetSeq (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (f : FunID) :=
    let spv := projw m (Reg sp) in
    if (512 <? spv)%Z 
    then Some (returnGen (returnSeq f))
    else None.

  Definition genInstrSeq
             (l : LayoutInfo) (t : TagInfo)
             (m : MachineState) (p : PolicyState)
             (dataP codeP callP : TagSet -> bool)
             (cm : CodeMap_Impl) (f nextF : FunID)
             (fSteps : list nat)
    : G (list (InstructionI * TagSet * FunID * Operations) * (list nat)) :=
    let fromInstr :=
        bindGen (genInstr l t m p cm dataP codeP f)
                (fun itf => returnGen ([itf])) in
    let '(fFuel, rest) :=
        match fSteps with
        | (S fFuel)::rest => (fFuel, rest)
        | O::rest => (O, rest)
        | _ => (O, [])
        end in
    let returnFreq := (funMaxFuel - fFuel)%nat in
    let instrFreq := (fFuel - 2)%nat in
    let callFreq := 1%nat in
    let instGen := bindGen fromInstr (fun g => ret (g,fFuel::rest)) in
    match genCall l t m p cm f nextF callP,
          genRetSeq m p cm f with
    | None, None => instGen
    | None, Some g2 =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest))) ])%nat
    | Some g1, None =>
      freq_ instGen ([ (instrFreq, instGen)
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest))) ])%nat
    | Some g1, Some g2 =>
      freq_ instGen ([ (instrFreq, bindGen fromInstr (fun g => ret (g,fFuel::rest)))
                       ; (callFreq, bindGen g1 (fun g => ret (g,funMaxFuel::fFuel::rest)))
                       ; (returnFreq, bindGen g2 (fun g => ret (g,rest)))
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
                                         (*               trace ("Trying to set: " ++ show k ++ " to " ++ show z ++ " which was " ++ show (fst c k) ++ nl ++ "Previous value was: " ++ show (proj macc k) ++ nl ++ " Next value will be: " ++ show (proj (jorp macc k z) k) ++ nl ++ nl)%string *)
                                         (returnGen (jorp macc k z)))
                end)
            )
            (getElements m) m .

  Definition genVariantByList (ks : list Element) (m : MachineState) : G MachineState :=
    foldGen (fun macc k =>
               match List.find (fun k' => keqb k k') ks with
               | Some _ => bindGen (genImm 40) (fun z => returnGen (jorp macc k z))
               | None => returnGen macc
               end)
          ks m.

  Instance ShowStuff : Show (InstructionI * TagSet * FunID * Operations) :=
    {| show '(i, ts, f, a) := (show i ++ "@" ++ show ts ++ "|" ++ show f)%string |}.
  
  (*
    -- | Generation by execution receives an initial machine X PIPE state and
    -- | generates instructions until n steps have been executed.
    -- | Returns the original machines with just the instruction memory locations
    -- | updated.
    genByExec :: PolicyPlus -> Int -> Machine_State -> PIPE_State ->
    (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
    (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
    Gen (Machine_State, PIPE_State)
   *)
  Fixpoint gen_exec_aux (steps : nat)
           (funSteps : list nat)
           (i : LayoutInfo) (t : TagInfo)
           (m0 : MachineState) (p0 : PolicyState)
           (m  : MachineState) (p  : PolicyState)
           (cm : CodeMap_Impl) (f : FunID) (nextF : FunID)
           (its : list (InstructionI * TagSet * FunID * Operations))
           (dataP codeP callP : TagSet -> bool)
    (* num calls? *)
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    (*trace ("GenExec..." ++ show steps ++ " " ++ show its ++ printPC m p ++ nl)%string*)
    match steps with
    | O =>
      (* Out-of-fuel: End generation. *)
      ret (m0, p0, cm)
    | S steps' =>
      match map.get (getMem m) (getPc m) with
      | Some _ =>
        match its with
        | nil =>
          (* Instruction already exists, step... *)
          match mpstep (m,p), funSteps with
          | Some ((m',p'),_t,o), (S n)::ns =>
            (* ...and recurse. *)
            gen_exec_aux steps' (n::ns) i t m0 p0 m' p' cm f nextF its codeP dataP callP 
          | Some ((m',p'),_t,o), _ =>
            gen_exec_aux steps' funSteps i t m0 p0 m' p' cm f nextF its codeP dataP callP 
          | _, _ =>
            (*trace "Something went wrong."*) ret (m0,p0,cm)
          end
        | _ =>
          (*trace ("Existing instruction mid-sequence" ++ nl)%string*)
          ret (m0, p0, cm)
        end
      | _ =>
        (* Check if there is anything left to put *)
        (bindGen
           (match its with
            | [] =>
              (* Generate an instruction sequence. *)
              (* TODO: Sequences, calls. *)
              bindGen (genInstrSeq i t m p dataP codeP callP cm f nextF funSteps)
                      (fun '(itfas,funSteps') =>
                         match itfas with
                         | (i,t,f',a) :: itfs' =>
                           (*trace (show (i,t,f',a) ++ nl)%string*)
                           (returnGen (a, f', (i,t), itfs',funSteps'))
                         | _ => exception "EmptyInstrSeq"
                         end)
            | ((i,t,f',a)::itfs') =>
              match funSteps with
              | (S n)::rest =>
                returnGen (a, f', (i,t), itfs', (n::rest))
              | _ =>
                returnGen (a, f', (i,t), itfs', funSteps)
              end
            end)
           (fun '(a, f', (is,it), its, funSteps') =>
              let nextF' := if Nat.eqb f' nextF then
                              S nextF else nextF in
              let m0' := setInstrI (getPc m) m0 is in
              let m'  := setInstrI (getPc m) m  is in
              let p0' := setInstrTagI (word.unsigned (getPc m)) p0 it in
              let p'  := setInstrTagI (word.unsigned (getPc m)) p it in
              let cm' := map.put cm (word.unsigned (getPc m)) (Some a) in
              match mpstep (m', p') with
              | Some ((m'', p''), _t, o) =>
                (gen_exec_aux steps' funSteps' i t m0' p0' m'' p'' cm' f' nextF' its dataP codeP callP)
              | _ =>
                (*trace ("Couldn't step" ++ nl(* ++  printMachine m' p' cm' ++ nl*))%string*)
                      ret (m0', p0', cm')
              end))
      end
    end.

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
    : G (MachineState * PolicyState * CodeMap_Impl) :=
    bindGen (genDataMemory i t m0 p0)
            (fun '(ms,ps) =>
               bindGen (genGPRs t ms ps)
                       (fun '(ms', ps') =>
                          (* Something about sp?
                             let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
                             ps' <- genGPRTs pplus ps (genGPRTag pplus)
                             let ps'' = ps' & pgpr . at sp ?~ spTag
                           *)
                          (gen_exec_aux maxFuel [funMaxFuel] i t ms' ps' ms' ps' cm0 O (S O)
                                        (initSeq O) dataP codeP callP))).

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
       ; pctags := [Tpc 0; Th2]
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
  let callP := fun tt => match tt with
                         | [Tinstr; Th1] => true
                         | _ => false
                         end in  
  genMachine defLayoutInfo defTagInfo zeroedRiscvMachine zeroedPolicyState map.empty
             dataP codeP callP.
End GenRISCVLazyNoDepth.
*)
