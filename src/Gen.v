Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.HexNotation. Require Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Spec.Machine.
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

Import RiscvMachine.

From StackSafety Require Import Machine.

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
                  (* ; rTag : Tag *)
                  }.

Record RegInfo := { dataPtr : list PtrInfo
                  ; codePtr : list PtrInfo
                  ; arith : list ArithInfo
                  }.

Record LayoutInfo := { instLo : Z
                     ; instHi : Z
                     ; dataLo : Z
                     ; dataHi : Z 
                     }.

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

Definition Tag := unit.
Definition groupRegisters (i : LayoutInfo) (m : MachineState) (p : PolicyState) : RegInfo :=
  let regs := getRegs m in

  (* Given range limits (low / high) for when something
     is valid, calculate the immediates involved. *)
  let getInfo (regTagP : Tag -> bool) lo hi rID rVal rTag :=
      if andb (regTagP rTag) (rVal <=? hi) then
        let minToAdd :=
            if rVal <=? lo then lo - rVal else 0 in
        Some {| pID := rID; pVal := rVal
              ; pMinImm := minToAdd
              ; pMaxImm := hi - rVal
              (* ; pTag := rTag *)
             |}
      else None
  in
  (* TODO: When tags... *)
  let dataTagP := fun tt => true in
  let codeTagP := fun tt => true in  
  let getDataInfo :=
      getInfo dataTagP (dataLo i) (dataHi i) in 
  let getCodeInfo :=
      getInfo codeTagP (instLo i) (instHi i) in 

  let dataRegs :=
      map.fold
        (fun acc rID rVal =>
           match getDataInfo rID (word.signed rVal) tt with
           | Some pi => pi :: acc
           | None => acc
           end) nil regs in
  let codeRegs :=
      map.fold (fun acc rID rVal =>
                  match getCodeInfo rID (word.signed rVal) tt with
                  | Some pi => pi :: acc
                  | None => acc
                  end) nil regs in
  let arithRegs :=
      map.fold (fun acc rID rVal =>
                  {| aID := rID |} :: acc) nil regs in
  
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
Definition genInstr (i : LayoutInfo) (m : MachineState) (p : PolicyState) : G (InstructionI * Tag) :=
  let groups := groupRegisters i m p in
  let a := arith groups in
  let d := dataPtr groups in
  let c := codePtr groups in

  let def_a := {| aID := 0 |} in
  let def_p := {| pID := 0; pVal := 0;
                  pMinImm := 0; pMaxImm := 0 |} in
  
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
          let tag := tt in
          ret (instr, tag)))))
       ; (onNonEmpty d 3%nat,
          bindGen (elems_ def_p d) (fun pi =>
          bindGen (genTargetReg m) (fun rd =>
          bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
          let imm := pMinImm pi + imm' in
          let instr := Lw rd (pID pi) imm in
          let tag := tt in
          ret (instr, tag)))))
       ; ((onNonEmpty d 3 * onNonEmpty a 1)%nat,
          bindGen (elems_ def_p d) (fun pi =>
          bindGen (genSourceReg m) (fun rs =>
          bindGen (genImm (pMaxImm pi - pMinImm pi)) (fun imm' =>
          let imm := pMinImm pi + imm' in
          let instr := Sw (pID pi) rs imm in
          let tag := tt in
          ret (instr, tag)))))
       ; (onNonEmpty a 1%nat,
          bindGen (elems_ def_a a) (fun ai1 =>
          bindGen (elems_ def_a a) (fun ai2 =>
          bindGen (genTargetReg m) (fun rd =>
          let instr := Add rd (aID ai1) (aID ai2) in
          let tag := tt in
          ret (instr, tag)))))
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
(*
-- Should return a maybe or be called only when the offset is guaranteed to exist
genCall :: PolicyPlus -> Machine_State -> PIPE_State ->
            (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
            (Instr_I -> Gen TagSet) ->
            (Integer -> [(Instr_I, TagSet)]) ->
            Gen [(Instr_I, TagSet)]
genCall pplus ms ps dataP codeP callP genInstrTag headerSeq = do
  let m = ms ^. fmem
      t = Map.assocs $ ps ^. pmem

      existingCallSites = map (\(i,t) -> (i - ms ^. fpc)) $ filter (\(i,t) -> callP t) t
      newCallSites =
        -- iterate through all possible instruction locations
        -- and filter out the ones that already exist in memory
        let offset_choices = [20, 24 .. (instrHigh pplus - instrLow pplus - 50)]
            valid_offsets = filter (\i -> ms ^. fpc + i < instrHigh pplus - 50) offset_choices
            not_used = filter (\i -> not (Map.member (ms ^. fpc + i) m)) valid_offsets
--        in traceShow (instrHigh pplus, instrLow pplus, instrHigh pplus - instrLow pplus - 50, offset_choices, valid_offsets, not_used) not_used
        in not_used        

      options = existingCallSites ++ newCallSites

  offset <-
    if any (\ off -> off + ms ^. fpc > 400) options then error $ show options else
    if not $ null options then elements options else return 4242 -- FIX
  return $ headerSeq offset
 *)
(*
-- TODO: This might need to be further generalized in the future
-- Returns (call diff, instruction sequence)
-- INV: Never returns empty list
genInstrSeq :: PolicyPlus -> Machine_State -> PIPE_State ->
               (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
               (Instr_I -> Gen TagSet) ->
               (Integer -> [(Instr_I, TagSet)]) -> Int -> [(Instr_I, TagSet)] ->
               Gen (Int, [(Instr_I, TagSet)]) 
genInstrSeq pplus ms ps dataP codeP callP genInstrTag headerSeq numCalls retSeq =
  frequency [ (5, (0,) <$> (:[]) <$> genInstr pplus ms ps dataP codeP genInstrTag)
            -- TODO: Sometimes generate calls in the middle of nowhere
            , (2, (1,) <$> genCall pplus ms ps dataP codeP callP genInstrTag headerSeq)
            -- TODO: Some times generate returns without the sequence
            , (numCalls, return (-1, retSeq))
            -- TODO: Sometimes read/write the instruction memory (harder to make work)
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

Definition genDataMemory (i : LayoutInfo) : G map.rep :=
  let idx := Zseq (dataLo i) (dataHi i) in
  let fix walk addrs mem :=
      match addrs with
      | [] => returnGen mem
      | a::addrs' =>
        bindGen (genImm (dataHi i)) (fun d =>
        walk addrs' (map.put mem a d))
      end in
  walk idx map.empty.

Definition setInstrI (m : MachineState) (i : InstructionI) : MachineState :=
  let prog := [encode i] in
  let addr := getPc m in
  withXAddrs
    (addXAddrRange addr (4 * Datatypes.length prog)
                   (getXAddrs m))
        (withMem
           (unchecked_store_byte_list addr
              (Z32s_to_bytes prog) (getMem m)) m).
  

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
genByExec pplus n init_ms init_ps dataP codeP callP headerSeq retSeq genInstrTag =
  exec_aux n init_ms init_ps init_ms init_ps [] 0
  where exec_aux :: Int -> Machine_State -> PIPE_State ->
                           Machine_State -> PIPE_State ->
                           [(Instr_I, TagSet)] ->
                           Int -> 
                           Gen (Machine_State, PIPE_State)
        exec_aux 0 ims ips ms ps generated numCalls = return (ims, ips)
        exec_aux n ims ips ms ps generated numCalls 
        -- Check if an instruction already exists
          | Map.member (f_pc ms) (f_dm $ f_mem ms) = do
            traceShowM ("Instruction exists, executing...") 
            case fetch_and_execute pplus ms ps of
              Right (ms'', ps'') ->
                -- TODO: Check that generated is empty here?
                exec_aux (n-1) ims ips ms'' ps'' [] numCalls
              Left err ->
                -- trace ("Warning: Fetch and execute failed with " ++ show n
                --        ++ " steps remaining and error: " ++ show err) $
                return (ims, ips)
          | otherwise = do
              traceShowM ("No instruction exists, generating...")
              -- Generate an instruction for the current state
              -- Checking if there is a "sequence" part left
              (numCalls', is, it, generated') <-
                case generated of
                  [] -> do --(\(is,it) -> (is,it,[])) <$>
--                          genInstr pplus ms ps dataP codeP genInstrTag
                           (cd, v) <- genInstrSeq pplus ms ps dataP codeP callP genInstrTag headerSeq numCalls retSeq
                           case v of
                             ((is,it):t) -> 
                                return (cd + numCalls, is,it,t)
                             _ -> error "empty instruction sequencer"
                  ((is,it):t) -> return (numCalls, is,it,t)
              traceShowM ("Generated:", is, it, generated')
              -- Update the i-memory of both the machine we're stepping...
              let ms' = ms & fmem . at (f_pc ms) ?~ (encode_I RV32 is)
                  ps' = ps & pmem . at (f_pc ms) ?~ it 
              -- .. and the i-memory of the inital pair _at the f_pc ms location_
                  ims' = ims & fmem . at (f_pc ms) ?~ (encode_I RV32 is)
                  ips' = ips & pmem . at (f_pc ms) ?~ it
              -- Proceed with execution
              -- traceShow ("Instruction generated...", is) $
              case fetch_and_execute pplus ms' ps' of
                Right (ms'', ps'') ->
                  -- trace "Successful execution" $
                  exec_aux (n-1) ims' ips' ms'' ps'' generated' numCalls'
                Left err ->
                  -- trace ("Warning: Fetch and execute failed with "
                  --       ++ show n ++ " steps remaining and error: " ++ show err) $
                  return (ims', ips')
 *)

Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.empty;
  getPc := ZToReg 0;
  getNextPc := ZToReg 4;
  getMem := map.empty;
  getXAddrs := nil;
  getLog := nil;
|}.

(*
                           
genGPRs :: Machine_State -> Gen Machine_State
-- Map GPR_Addr GPR_Val -> Gen (Map GPR_Addr GPR_Val) 
genGPRs m = do
  ds <- replicateM 3 $ genImm 40
  return $ m & fgpr %~ Map.union (Map.fromList $ zip [minReg..] ds)

genGPRTs :: PolicyPlus -> PIPE_State -> Gen TagSet -> Gen PIPE_State
genGPRTs pplus p genGPRTag = do 
  cs <- replicateM 3 genGPRTag
  return $ p & pgpr %~ Map.union (Map.fromList $ zip [minReg..] cs)
-- TODO:  move sptag stuff from genMachine to here

genMachine :: PolicyPlus -> (PolicyPlus -> Gen TagSet) -> (PolicyPlus -> Gen TagSet) ->
             (TagSet -> Bool) -> (TagSet -> Bool) -> (TagSet -> Bool) ->
             (Integer -> [(Instr_I, TagSet)]) -> [(Instr_I, TagSet)] ->
             (Instr_I -> Gen TagSet) -> TagSet -> 
             Gen RichState
genMachine pplus genMTag genGPRTag dataP codeP callP headerSeq retSeq genITag spTag = do

  -- | Initial memory
  (mm,pm) <- genDataMemory pplus genMTag
  let ms = initMachine
             & fmem_mem .~ mm 
--             & fmem . at (f_pc initMachine) ?~ (encode_I RV32 $ JAL 0 1000) 
      ps = init_pipe_state pplus
             & pmem_mem .~ pm
--             & pmem . at (f_pc ms) ?~ (emptyInstTag pplus) 

  -- | Update registers
  ms' <- genGPRs  ms
  let ms'' = ms' & fgpr . at sp ?~ (instrHigh pplus + 4)
  ps' <- genGPRTs pplus ps (genGPRTag pplus)
  let ps'' = ps' & pgpr . at sp ?~ spTag

  -- | Do generation by execution
  (ms_fin, ps_fin) <- genByExec pplus maxInstrsToGenerate ms'' ps'' dataP codeP callP headerSeq retSeq genITag

  return $ Rich ms_fin ps_fin
*)
