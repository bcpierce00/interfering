Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.HexNotation.
Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List. 

Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.RegisterNames.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.MinimalCSRsDet.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import riscv.Utility.ExtensibleRecords. Import HnatmapNotations. Open Scope hnatmap_scope.
Require coqutil.Map.SortedList.

Import ListNotations.
Import RiscvMachine.

From StackSafety Require Import MachineImpl.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From QuickChick Require Import QuickChick.
Import QcNotation.

Definition r0 : Register := 0.
Definition ra : Register := 1.
Definition sp : Register := 2.

(*- TODO: Sometimes we might want to use/target ra and sp to inject/find bugs? *)
Definition minReg : Register := 8.
Definition noRegs : nat := 3%nat.
Definition maxReg : Register := minReg + Z.of_nat noRegs.

(* Generate a random register for source, can include r0 *)
Definition genSourceReg (m : MachineState) : G Register :=
  freq [ (1%nat, ret r0)
       ; (noRegs, choose (minReg, maxReg))
       ].

Definition genTargetReg (m : MachineState) : G Register :=
  choose (minReg, maxReg).

Definition genImm (n : Z) : G Z :=
  bindGen (choose (0, Z.div n 4))
          (fun n' => ret (Z.mul 4 n')).

Record ArithInfo := { aID : Register }.

Record PtrInfo := { pID     : Register
                  ; pVal    : Z
                  ; pMinImm : Z
                  ; pMaxImm : Z
                  ; pTag : TagSet
                  }.

Record RegInfo := { dataPtr : list PtrInfo
                  ; codePtr : list PtrInfo
                  ; arith : list ArithInfo
                  }.

Record LayoutInfo := { instLo : Z
                     ; instHi : Z
                     ; dataLo : Z
                     ; dataHi : Z
                     ; stack  : Z
                     }.

Definition defLayoutInfo :=
  {| dataLo := 1000
   ; dataHi := 1020
   ; instLo := 0
   ; instHi := 400
   ; stack  := 500
  |}.                 

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

(* map utils *)
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

(* Printing *)
Instance ShowWord : Show word :=
  {| show x := show (word.signed x) |}.

Definition printGPRs (m : MachineState) (p : PolicyState) :=
  List.fold_right (fun '(rID, rVal, rTag) acc =>
                     show rID ++ " : " ++ show rVal ++ " @ " ++ show rTag ++ nl ++ acc)%string ""
                  (listify2 (getRegs m) (regtags p)). 

Definition listify1_word mem := 
  List.rev
    (map.fold
       (fun acc k v =>
          (* Keep mod 4 *)
          if Z.eqb (snd (Z.div_eucl (word.unsigned k) 4)) 0
          then
            let val := 
                match loadWord mem k with
                | Some w32 => LittleEndian.combine _ w32
                | _ => 42424242
                end in
            (word.unsigned k,val) :: acc
          else acc) nil mem).

Definition CodeMap_Impl := Zkeyed_map CodeStatus.
Definition CodeMap_fromImpl (cm : CodeMap_Impl) : CodeMap :=
  fun addr => match map.get cm addr with
              | Some cs => cs
              | _ => notCode
              end.

Instance ShowCodeAnnotation : Show CodeAnnotation :=
  {| show ca :=
       match ca with
       | call => "call"
       | yield => "yield"
       | scall _ => "scall"
       | normal => "normal"
       | _  => "ret"
       end |}.
Derive Show for CodeStatus.

Definition printMem (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (i : LayoutInfo) :=
  let mem := getMem m in
  let tags := memtags p in
  let mts := combine_match (listify1_word mem) (listify1 tags) in
  List.fold_right
    (fun '(k,val,t) s =>
       let printed :=
           if andb (Z.leb (instLo i) k)
                   (Z.leb k (instHi i))
           then
             match decode RV32I val with
             | IInstruction inst =>
               (show inst ++ " @ " ++ show t ++ " < " ++ show (CodeMap_fromImpl cm k) ++ " >")%string
             | _ => (show val ++ " <not-inst>")%string
             end
           else (show val ++ " @" ++ show t ++ " < " ++ show (CodeMap_fromImpl cm k) ++ " >")%string in
       (show k ++ " : " ++ printed ++ nl ++ s)%string
    ) "" mts.

Definition printPC (m : MachineState) (p : PolicyState) :=
  (show (word.unsigned (getPc m)) ++ " @ " ++ show (pctags p))%string.

Definition printMachine
           (m : MachineState) (p : PolicyState) cm := (
  "PC:" ++  
  printPC m p ++ nl ++
  "Registers:" ++ nl ++
  printGPRs m p ++ nl ++
  "Memory: " ++ nl ++
  printMem m p cm defLayoutInfo ++ nl
  )%string.

Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
  {| show := fun '(m,p,cm) => printMachine m p cm |}.

(*
, initGPR :: TagSet 
  , initMem :: TagSet 
  , initPC  :: TagSet 
  , initNextColor :: Color
  , emptyInstTag :: TagSet
  -- Memory layout: Instr mem ... stack | data mem
  -- Stack pointer should begin at dataMemLow - 4?
  , instrLow    :: !Integer
  , instrHigh   :: !Integer
  , dataMemLow  :: !Integer
  , dataMemHigh :: !Integer
*)
  
(* TODO: Policy state once that's done *)
(*
groupRegisters :: PolicyPlus -> GPR_File -> GPR_FileT ->
                  (TagSet -> Bool) -> (TagSet -> Bool) ->
                  RegInfo
groupRegisters pplus (GPR_File rs) (GPR_FileT ts) dataP codeP =
*)
(*
-- dataP, codeP : Predicates over the tagset to establish potential invariants for code/data pointers.
-- Picks out valid (data registers + content + min immediate + max immediate + tag),
--                 (jump registers + min immediate),
--                 integer registers
 *)

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
      getInfo (noSp dataP) (dataLo i) (dataHi i) in 
  let getCodeInfo :=
      getInfo (noSp codeP) (instLo i) (instHi i) in 

  
  let dataRegs :=
      List.fold_right
        (fun '(rID, rVal, rTag) acc =>
           match getDataInfo rID (word.signed rVal) rTag with
           | Some pi => pi :: acc
           | None => acc
           end) nil (listify2 regs tags) in
  let codeRegs :=
      List.fold_right
        (fun '(rID, rVal, rTag) acc =>
           match getCodeInfo rID (word.signed rVal) rTag with
           | Some pi => pi :: acc
           | None => acc
           end) nil (listify2 regs tags) in

  let arithRegs :=
      List.fold_right
        (fun '(rID, rVal, rTag) acc =>
           if noSp (fun _ => true) rTag then
             {| aID := rID |} :: acc
           else acc) nil (listify2 regs tags) in
  
  {| codePtr := codeRegs
   ; dataPtr := dataRegs
   ; arith   := arithRegs
   |}.

(*
-- TODO: This might need to be further generalized in the future
genInstr :: PolicyPlus -> Machine_State -> PIPE_State ->
            (TagSet -> Bool) -> (TagSet -> Bool) ->
            (Instr_I -> Gen TagSet) -> Gen (Instr_I, TagSet)
*)
Definition genInstr (i : LayoutInfo) (t : TagInfo)
           (m : MachineState) (p : PolicyState)
           (dataP codeP : TagSet -> bool)
           (genInstrTag : InstructionI -> G TagSet)
  : G (InstructionI * TagSet) :=
  let groups := groupRegisters i t m p dataP codeP in
  let a := arith groups in
  let d := dataPtr groups in
  let c := codePtr groups in

  let def_a := {| aID := 0 |} in
  let def_dp := {| pID := 0; pVal := 0;
                   pMinImm := 0; pMaxImm := 0;
                   pTag := dataTag t
                |} in
  
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
          ret (instr, tag))))))
(*       ; (onNonEmpty d 3%nat,
          bindGen (elems_ def_dp d) (fun pi =>
          bindGen (genTargetReg m) (fun rd =>
          bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
          let imm := pMinImm pi + imm' in
          let instr := Lw rd (pID pi) imm in
          bindGen (genInstrTag instr) (fun tag =>
          ret (instr, tag)))))) *)
(*       ; ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
          bindGen (elems_ def_dp d) (fun pi =>
          bindGen (genSourceReg m) (fun rs =>
          bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
          let imm := pMinImm pi + imm' in
          let instr := Sw (pID pi) rs imm in
          bindGen (genInstrTag instr) (fun tag => 
          ret (instr, tag)))))) *)
       ; (onNonEmpty a 1%nat,
          bindGen (elems_ def_a a) (fun ai1 =>
          bindGen (elems_ def_a a) (fun ai2 =>
          bindGen (genTargetReg m) (fun rd =>
          let instr := Add rd (aID ai1) (aID ai2) in
          bindGen (genInstrTag instr) (fun tag => 
          ret (instr, tag))))))
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


Definition Zseq (lo hi : Z) :=
  let len := Z.to_nat (Z.div (hi - lo) 4) in
  let fix aux start len :=
      match len with
      | O => []
      | S len' => start :: aux (start + 4) len'
      end in
  aux lo len.

Definition headerSeq offset :=
  [ (Jal ra offset, [Tinstr; Tcall])
  ; (Sw sp ra 0  , [Tinstr; Th1])
  ; (Addi sp sp 12, [Tinstr; Th2])
  ].
(* Based on Rob's 
  (* 08 *) IInstruction (Sw SP RA 0); (* H1 *)
  (* 12 *) IInstruction (Addi SP SP 12); (* H2 *)
*)
Definition returnSeq :=
  [ (Lw ra sp (-4), [Tinstr; Tr1])
  ; (Addi sp sp 8 , [Tinstr; Tr2])
  ; (Jalr ra ra 0 , [Tinstr; Tr3])
  ].

Definition genCall (l : LayoutInfo) (t : TagInfo)
           (m : MachineState) (p : PolicyState)
           (cm : CodeMap_Impl) (nextF : FunID)
           (callP :  TagSet -> bool) :
  option (nat * G (list (InstructionI * TagSet) * FunID))
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
                  match map.get cm i with
                  | Some (inFun f _) =>
                    (headerSeq i, f) 
                  | _ => exception "genCall - nofid"
                  end) existingSites  in
  let newOpts :=
      List.map (fun i => (headerSeq i, nextF)) newCallSites in
  match exOpts ++ newOpts with
  | [] => None
  | x :: xs =>
    Some (S (List.length xs), elems_ x (x :: xs))
  end.

Definition genInstrSeq
           (l : LayoutInfo) (t : TagInfo)
           (m : MachineState) (p : PolicyState)
           (dataP codeP callP : TagSet -> bool)
           (cm : CodeMap_Impl) (f nextF : FunID)
           (genInstrTag : InstructionI -> G TagSet) :=
  let fromInstr :=
      bindGen (genInstr l t m p dataP codeP genInstrTag)
              (fun it => returnGen ([it], f)) in
  match genCall l t m p cm f callP with
  | None => fromInstr
  | Some (len,g) =>
    freq_ g (cons (2%nat, g)
                  (cons (5%nat, fromInstr)
                        nil))
  end.

Definition replicateGen {A} (n : nat) (g : G A) : G (list A) :=
  let fix aux n :=
      match n with
      | O => returnGen nil
      | S n' => liftGen2 cons g (aux n')
      end in
  aux n.

Definition genDataMemory
           (i : LayoutInfo) (t : TagInfo)
           (m : MachineState) (p : PolicyState)
  : G (MachineState * PolicyState) :=
  let idx := Zseq (dataLo i) (dataHi i) in
  bindGen (replicateGen (List.length idx) (genImm (dataHi i)))
  (fun vals =>           
  bindGen (replicateGen (List.length idx) (returnGen (dataTag t)))
  (fun tags =>           
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
         (its : list (InstructionI * TagSet))
         (dataP codeP callP : TagSet -> bool)
         (genInstrTag : InstructionI -> G TagSet)
         (* num calls? *)
  : G (MachineState * PolicyState * CodeMap_Impl) :=
  trace (show ("GenExec...", steps, its, printPC m p) ++ nl)%string
  (match steps with
  | O =>
    (* Out-of-fuel: End generation. *)
    ret (m0, p0, cm)
  | S steps' =>
    match map.get (getMem m) (getPc m) with
    | Some _ =>
      trace ("Existing instruction found: " ++ nl)%string
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
      trace ("No instruction found " ++ nl)%string
      (* Check if there is anything left to put *)
      (bindGen (match its with
               | [] =>
                 (* Generate an instruction sequence. *)
                 (* TODO: Sequences, calls. *)
                 bindGen (genInstrSeq i t m p dataP codeP callP cm f nextF genInstrTag)
                         (fun '(ists, f') =>
                            match ists with
                            | ist :: ists' =>
                              trace (show (f',ist, ists') ++ nl)%string
                                    (returnGen (f', ist, ists'))
                            | _ => exception "EmptyInstrSeq"
                            end)
               | ist::its' =>
                 returnGen (f, ist, its')
               end)
      (fun '(f', (is,it), its) =>
         let nextF' := if Nat.eqb f' nextF then
                         S nextF else nextF in
         let m0' := setInstrI (getPc m) m0 is in
         let m'  := setInstrI (getPc m) m  is in
         let p0' := setInstrTagI (word.unsigned (getPc m)) p0 it in
         let p'  := setInstrTagI (word.unsigned (getPc m)) p it in
         let cm' := map.put cm (word.unsigned (getPc m)) (inFun f' normal) in
         match mpstep (m', p') with
         | Some ((m'', p''), o) =>
           trace ("PC after mpstep: " ++ show (word.unsigned (getPc m'')) ++ nl)%string 
                 (gen_exec_aux steps' i t m0' p0' m'' p'' cm' f nextF' its dataP codeP callP genInstrTag)
         | _ =>
           trace ("Couldn't step" ++ nl ++  printMachine m' p' cm' ++ nl)%string
                 (ret (m0', p0', cm'))
         end))
    end
  end).

Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.put (map.put map.empty sp (word.of_Z 500))
                     ra (word.of_Z 0);
  getPc := ZToReg 0;
  getNextPc := ZToReg 4;
  getMem := map.empty;
  (*unchecked_store_byte_list (word.of_Z 500)
                                      (Z32s_to_bytes (cons 0 nil))
                                      (map.empty); *)
  getXAddrs := nil; 
  getLog := nil;
|}.


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

(*
genGPRTs :: PolicyPlus -> PIPE_State -> Gen TagSet -> Gen PIPE_State
genGPRTs pplus p genGPRTag = do 
  cs <- replicateM 3 genGPRTag
  return $ p & pgpr %~ Map.union (Map.fromList $ zip [minReg..] cs)
-- TODO:  move sptag stuff from genMachine to here
 *)

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
  bindGen (genDataMemory i t m0 p0) (fun '(ms,ps) =>
  bindGen (genGPRs t ms ps) (fun '(ms', ps') =>

  (* Something about sp?
  let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
  ps' <- genGPRTs pplus ps (genGPRTag pplus)
  let ps'' = ps' & pgpr . at sp ?~ spTag
  *)

  (gen_exec_aux 40 i t ms' ps' ms' ps' cm0 O (S O) nil dataP codeP callP genInstrTag))).

Definition zeroedPolicyState : PolicyState :=
  {| nextid := 0
   ; pctags := [Tpc 0]
   ; regtags := map.put (map.put map.empty ra nil) sp (cons Tsp nil)
   ; memtags := map.empty (* map.put map.empty 500 (cons Tsp nil) *)
  |}. 

(* Specialized to current policy *)
Definition genMach :=
  let codeP := fun tt => true in
  let dataP := fun tt => true in
  (* Fix this *)
  let callP := fun tt => false in  
  let genInstrTag : InstructionI -> G TagSet :=
      fun i => returnGen (cons Tinstr nil) in
  genMachine defLayoutInfo defTagInfo zeroedRiscvMachine zeroedPolicyState map.empty
             dataP codeP callP genInstrTag.

From StackSafety Require Import SubroutineSimple.

Sample1 (genMach).

(*
Definition prop_integrity :=
  let cm := fun _ => notCode in
  let sm := fun _ => true in
  forAll genMach (fun '(m,p) =>
  (SimpleStackIntegrityStepP cm 42 m p (initC sm))).
*)
(* QuickCheck prop_integrity. *)
