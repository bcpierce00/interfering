From StackSafety Require Import MachineModule PolicyModule TestingModules
     RISCVMachine Lazy DefaultLayoutLazy PrintLazy.

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

Require Import ExtLib.Structures.Monad. Import MonadNotation. Open Scope monad_scope.

Definition trace := false.
Notation " S '!' A " := (if trace then Show.trace (S)%string A else A)
                          (at level 60).

Module GenRISCVLazyOrig <: Gen RISCVLazyOrig RISCVLazyDef.
  Import RISCVLazyOrig.
  Import TagPolicyLazyOrig.
  Import RISCVLazyDef.
  Module PM := PM.
  Import PM.
  Import PrintRISCVLazyOrig.

  Definition maxFuel := 100%nat.
  Definition funMaxFuel := 10%nat.

  Definition noops : list Operation := [].
  
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

  (* Some helpers for initializing states *)

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

  Inductive localKind :=
  | Lpublic
  | Lsecret
  .

  Derive Show for localKind.

  Record FunctionProfile :=
    mkfunprofile {
        id : FunID;
        entry : Addr;
        tc_entry : option Addr;
        register_args : list Register;
        relative_args : nat;
        reference_args : list (Register * Z); (* argument register, size (words) *)
        locals : list (positive * localKind);
        callee_save_regs : nat; (* simple layout: assume a range of consecutive
                                   registers starting from [minCalleeReg], no
                                   greater than the block of saved registers *)
      }.

  (* Constants to bound the complexity of generate functions. Note that
     arguments add a good number of instructions for boilerplate, limiting the
     complexity of functions of a given size (one may want to allocate more
     space for function generation to account for this). *)
  Definition MAX_REL_ARGS : nat := 1.
  Definition MAX_REF_ARGS : nat := 1.
  Definition MAX_LOCAL_WORDS : nat := 2.
  Definition MAX_CALLEE_SAVE_REGS : nat := noCalleeRegs.
  (* Quick consistency checks *)
  Goal (MAX_LOCAL_WORDS >= MAX_REF_ARGS)%nat. now constructor. Qed.

  Definition frameDataWords (fp : FunctionProfile) : Z :=
    let words_rel_args := Z.of_nat MAX_REL_ARGS in
    let words_locals := Z.of_nat MAX_LOCAL_WORDS in (* includes ref_args *)
    words_rel_args + words_locals.

  (* If we want to allocate everything at once, we need to know the amount of
     space we need to pass arguments to any of our callees (whom we need not
     know in advance). The callee's function profile would be used by the caller
     to extend its frame before the call. *)
  Definition frameSizeWords (fp : FunctionProfile) : Z :=
    let words_ra := 1 in
    let words_data := frameDataWords fp in
    let words_callee_save_regs := Z.of_nat MAX_CALLEE_SAVE_REGS in
    let trai_hack := 1 in (* HACK see notes in file *)
    words_ra + words_data + words_callee_save_regs + trai_hack.

  Definition frameSizeBytes (fp : FunctionProfile) : Z :=
    4 * frameSizeWords fp.

  Definition genImm (n : Z) : G Z :=
    if (n >=? 0)
    then bindGen (choose (0, Z.div n 4))
                 (fun n' => ret (Z.mul 4 n'))
    else ret 0.

  Definition genTargetReg (m : MachineState) : G Register :=
    freq [ (noRegs, choose (minReg, maxReg))
         ; (noCalleeRegs, choose (minCalleeReg, maxCalleeReg))
      ].

  Definition genSourceReg (m : MachineState) : G Register :=
    freq [ (1%nat, ret r0)
         ; (noRegs, choose (minReg, maxReg))
         ; (noCalleeRegs, choose (minCalleeReg, maxCalleeReg))
      ].

  (* Current valid offsets span a contiguous region of each function's
     (fixed-sized) frame. The topmost word is reserved for callee
     RAs. The bottommost words are reserved for callee-saved register
     storage and the current hacky padding word.

     Valid local offsets start from -8 (second topmost word in the
     frame). *)
  Definition genLocalOffset (fp : FunctionProfile) : G (option Z) :=
    let dataSize := frameDataWords fp in
    if 0 <? dataSize
    then off <- choose (0,dataSize-1);; ret (Some (-4*off - 8))
    else ret None.

  (* For attackers, maybe we want some added flexibility?
     Add tags to protect callee-saved copies or find extra attacks *)
  Definition allLocalOffsets (fp : FunctionProfile) : list Z :=
    let dataSizeN := Z.to_nat (frameDataWords fp) in
    let fix each n :=
      match n with
      | O => []
      | S n' => (-4 * (Z.of_nat n) - 4)::each n'
      end in
    each dataSizeN.
  
  Definition if_true_n (b:bool) (n:nat) :=
    if b then n else O.

  Open Scope nat.
  
  Definition stackbasedWrite (off : Z) (rs : Register) : InstructionI := Sw sp rs off.
  
  Definition stackbasedRead (off : Z) (rd : Register) : InstructionI := Lw rd sp off.

  Definition genLocalWrite (m : MachineState) (fp : FunctionProfile)
             (arg : bool) (retv : bool) (ooff : option Z) :
    G (list (InstructionI * TagSet * FunID * list Operation)) :=
    ooff' <- (match ooff with
              | Some off => ret ooff
              | None => genLocalOffset fp
              end);;
    match ooff' with
    | Some off =>
        reg <- (if arg
                then elems_ 0%Z (fp.(register_args))
                else if retv
                     then ret a0
                     else genSourceReg m);;
        let instr := stackbasedWrite off reg in
        ret ([(instr, [Tinstr], fp.(id), [])])
    | None =>
        ret ([((Addi 0 0 0)%Z, [Tinstr], fp.(id), [])])
    end.

  (* ROB: create an equivalent of genLocalWrite, genArgWrite that takes a second callee profile and
     might write into either:
     - rel/ref-arguments, if the callee has them
-    - the caller's Public locals
     You won't need an equivalent of arg or ooff. *)
  
  Definition genLocalRead (m : MachineState) (fp : FunctionProfile) :
    G (list (InstructionI * TagSet * FunID * list Operation)) := 
    ooff <- genLocalOffset fp;;
    match ooff with
    | Some off =>
        reg <- genTargetReg m;;
        let instr := stackbasedRead off reg in
        ret ([(instr, [Tinstr], fp.(id), [])])
    | None =>
        ret ([((Addi 0 0 0)%Z, [Tinstr], fp.(id), [])])
    end.

  Definition genPtrWrite (m : MachineState) (fp : FunctionProfile) (safe : bool) :
    G (list (InstructionI * TagSet * FunID * list Operation)) := 
    rd <- genTargetReg m;;
    rs <- genSourceReg m;;
    match safe, projt (snd m) (Reg rs) with
    | _,[Tvar _]  | true, _ =>
        let instr := Lw rd rs 0 in
        ret ([(instr, [Tinstr], fp.(id), [])])
    | _, _ =>
        ret ([((Addi 0 0 0)%Z, [Tinstr], fp.(id), [])])
    end.
  
  Definition genPtrRead (m : MachineState) (fp : FunctionProfile) (safe : bool) :
    G (list (InstructionI * TagSet * FunID * list Operation)) := 
    rd <- genTargetReg m;;
    rs <- genSourceReg m;;
    match safe, projt (snd m) (Reg rs) with
    | _, [Tvar _] | true, _ =>
        let instr := Lw rd rs 0 in
        ret ([(instr, [Tinstr], fp.(id), [])])
    | _, _ =>
        ret ([((Addi 0 0 0)%Z, [Tinstr], fp.(id), [])])
    end.
  
  (* ROB: similar to genArgWrite, create a genArgRead that reads from rel/ref args if available.
     It won't have a second function profile. *)
  
(* Helpful argument stuff from Rob, to reuse later. *)
(*
    let nth_rel_arg p :=
      match ofprof with
      | Some fprof => (fprof.(relative_args) <=? (Pos.to_nat p))%nat
      | None => false
      end in
    let frameSize :=
      match ofprof with
      | Some fprof => 4 * frameSizeWords fprof
      | None => 0
      end in
    let has_ref_arg :=
      match ofprof with
      | Some fprof => (List.length fprof.(reference_args) =? 1)%nat
      | None => false
      end in
    rd <- genTargetReg mp;;
    freq [ (10%nat, ret (Lw rd sp (-4)))
           ; (10%nat, ret (Lw rd sp (-8)))
           ; (if_true_n (512 <? spVal) 1%nat, ret (Lw rd sp (-12)))
           ; (if_true_n (516 <? spVal) 2%nat, ret (Lw rd sp (-16)))
           ; (if_true_n (520 <? spVal) 2%nat, ret (Lw rd sp (-20)))
           ; (1%nat, bindGen (choose (spVal - 500, spVal))
                             (fun off => ret (Lw rd sp (- off))))
           ; (1%nat, bindGen (choose (0, 600 - spVal))
                             (fun off => ret (Lw rd sp off)))
           (* relative arguments
              quick and dirty, related to MAX_REL_ARGS
              generate programmatically later *)
           ; (if_true_n (nth_rel_arg 1%positive) 1%nat, ret (Lw rd sp (-frameSize - 4)))
               (* ; (if_true_n (nth_rel_arg 2%positive) 1%nat, ret (Lw rd sp (-frameSize - 8))) *)
               (* ; (if_true_n (nth_rel_arg 3%positive) 1%nat, ret (Lw rd sp (-frameSize - 12))) *)
           (* reference arguments
              quick and dirty, similar to relative arguments
              now technically a stack read, could be more general *)
           ; (if_true_n has_ref_arg 1%nat, ret (Lw rd argReg 0))
      ].*)
  
  Definition genArith (i : LayoutInfo) (t : TagInfo)
             (m : MachineState) (cm : CodeMap_Impl)
             (f : FunID)
    : G (InstructionI * TagSet * FunID * list Operation) :=
    let noops : list Operation := [] in
    freq [(1, rs <- genSourceReg m ;;
              rd <- genTargetReg m;;
              imm <- genImm (dataHi i);;
              let instr := Addi rd rs imm in
              ret (instr, [Tinstr], f, noops));
          (1, rs1 <- genSourceReg m;;
              rs2 <- genSourceReg m;;
              rd <- genTargetReg m;;
              let instr := Add rd rs1 rs2 in
              ret (instr, [Tinstr], f, noops)) ].

  (* ROB: expand this with operations other than addition. *)

  (* This is from Leo's old tag-aware code-gen. Mine as needed. *)
(*    let def_dp := {| pID := 0; pVal := 0;
                     pMinImm := 0; pMaxImm := 0;
                     pTag := dataTag t
                  |} in*)

      (*  trace (show (l, badPtr groups)%string) *)
  
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

  Close Scope nat.
  Open Scope Z.

  Fixpoint count_list (n:nat) :=
    match n with
    | O => []
    | S n' => (Z.of_nat n'+3)::count_list n'
    end.

  (*
    relative arguments: list of Z offsets

    current:
    - caller stores arguments in its own stack frame
    - call (Tcall)
    - callee opens by storing RA at SP (Th1) and allocating its own frame (Th2)

    new:
    - tag arguments with (ARG depth) following Nick and André
    - rules for writing (caller) and reading (callee)
    - callers *must* allocate/store relargs
      - part of an extended call (and return) sequence?
      - callers must know the callee profile in advance (generation?)
      - for now, store freshly generated constants as arguments
    - callees *may* read from/write to relargs
    - to simplify, make relargs into a continuous range right below SP?
      - in any case, need to generate reads in the right range
      - other argument types will add some complexity to the scheme

    simplification 1:
    - as above
    - ignore locals and other types of arguments for now
    - [Caller frame] [Args] | [RA] [Callee frame]
      - where | is the stack pointer before the callee moves it

    simplification 2:
    - additionally, assume a maximum number of relative arguments
    - no need for additional stack (de)allocation

    argument clearing:
    - in both cases
    - leftover relative arguments may be read by subsequent callees
    - the usual issue with depth-based lazy policies
   *)

  (*
    reference arguments: list of registers and sizes

    new:
    - add a section of local stack variables below relargs
      - for simplicity, start with a private area of fixed size
      - we continue allocating full frames all at once
    - [Caller frame] [Locals] [Relargs] | [RA] [Callee frame]
    - callers *may* pass pointers into their private memory to callees
      - initially sharing at fixed single-word granularity
      - select one slot deterministically or pick from available area
    - callees *may* then read and write to shared memory
      - attention: argument registers may be overwritten!
      - (rule this out statically for now?)
    - attention: uninitialized/garbage locals?
   *)
  Fixpoint genLocals (n:nat) : G (list (positive * localKind)) :=
    match n with
    | O => ret []
    | S n' =>
        rest <- genLocals n';;
        public <- elems [Lpublic;Lsecret];;
        ret ((1%positive,public)::rest)
    end.

  Fixpoint localsByName (locs : list (positive * localKind)) : list (nat * Z * localKind) :=
    match locs with
    | [] => []
    | (sz,k)::locs' =>
        let ofl := localsByName locs' in
        let next := match ofl with
                    | [] => 0
                    | (_,off,_)::_ => off
                    end in
        (length ofl, next - (4*(Zpos sz)), k)::ofl
    end.
  
  (* TODO: Fill in the different kinds of arguments, etc.!*)
  Definition genFun (id:FunID) (addr:Addr) : G FunctionProfile :=
    reg_args <- choose (0,3)%nat;; (* Maxing out on 3 argument registers currently *)
    rel_args <- choose (0,MAX_REL_ARGS)%nat;;
    ref_args_count <- choose (0,MAX_REF_ARGS)%nat;;
    let ref_args := List.repeat (argReg, 1) ref_args_count in
    (* local_count <- choose (0,3)%nat;; *)
    let local_count := MAX_LOCAL_WORDS in
    locals <- genLocals local_count;;
    let spilled_regs := MAX_CALLEE_SAVE_REGS%nat in (* later: choose (and tweak generation!) *)
    ret (mkfunprofile id addr (Some (addr + 8)) (count_list reg_args) rel_args ref_args locals spilled_regs).
  
  Definition main : FunctionProfile :=
    mkfunprofile O 0 (Some 8) [] 0 [] [(3%positive,Lsecret)] 0.

    Fixpoint split3 (xs:list (instr * list Operation)) :=
    match xs with
    | [] => ([],[],[])
    | (inst,t,ops)::xs' =>
        let '(insts,ts,opss) := split3 xs' in
        (inst::insts,t::ts,ops::opss)
    end.

  Fixpoint add_addr {X:Type} (xs:list X) (base:Z) : list (Z*X) :=
    match xs with
    | [] => []
    | x::xs' =>
        (base, x)::add_addr xs' (base+4)
    end.
  
  Fixpoint genFuns (n : nat) (m : MachineState) : G (MachineState * (list FunctionProfile) * CodeMap_Impl) :=
    match n with
    | O => ret (m, [], map.empty)
    | S n =>
        let base := (Z.of_nat n) * 1000 in
        '(m',fps,cm) <- (genFuns n m);;
        fp <- (if n =? O then ret main else genFun n (base))%nat;;
        let sz := frameSizeWords fp in
        let '(insts,ts,opss) := split3 (head sz) in
        let m'' := setInstrs (add_addr insts base) m' in
        let m''' := setMemTags (add_addr ts base) m'' in
        let cm' := map.putmany_of_list (add_addr (map Some opss) base) cm in
        ret (m''', fp::fps, cm')
    end.

  Definition callHead
             offset f (i : LayoutInfo) (m : MachineState) (callee:FunctionProfile)
             (tail : bool)
    : G (list (InstructionI * TagSet * FunID * list Operation)) :=
    (* pass relative arguments (generated constants) *)
    (* quick and dirty, related to MAX_REL_ARGS, programmatically later *)
    rt <- (genTargetReg m);;
    imm1 <- (genImm (dataHi i));;
    imm2 <- (genImm (dataHi i));;
    let args :=
      if (callee.(relative_args) =? 1)%nat
      then [(Addi rt 0 imm1, [Tinstr],          f, [(*noops*)]);
            (Sw sp rt (-4),  [Tinstr; Tsetarg], f, [(*noops*)])]
      else [] in
    let call_args :=
      if (callee.(relative_args) =? 1)%nat
      then [(sp, -4, 4)]
      else [] in
    let refs :=
      if (List.length callee.(reference_args) =? 1)%nat
      then let hd := nth_default (0, 0) callee.(reference_args) 0 in
           [(Addi rt 0 imm2,       [Tinstr],         f, [(*noops*)]);
            (Sw sp rt (-8),        [Tinstr; Tvar 0], f, [(*noops*)]);
            (Addi argReg sp (-8),  [Tinstr; Tvar 0], f, [(*noops*)])]
      else [] in
    let refs_args :=
      if (List.length callee.(reference_args) =? 1)%nat
      then [(sp, -8, 4)] (* or (argReg _ _) *)
      else [] in
    let ops := if tail then [(Tailcall callee.(id) callee.(register_args) (call_args ++ refs_args))]
               else [(Call callee.(id) callee.(register_args) (call_args ++ refs_args))] in
    ret
      (args ++ refs ++
         [(
             Jal ra (offset - (4*(Z.of_nat (length args))) - (4*(Z.of_nat (length refs)))),
             [Tinstr; if tail then Ttailcall else Tcall],
             f,
             ops
         )]
      ).
  
  Definition returnSeq (f : FunID) (fp : FunctionProfile) :=
    let sz := frameSizeBytes fp in
    [ (* restore callee-saved registers
         HACK one word above frame lower bound *)
      (Lw   minCalleeReg       sp (-sz + 12), [Tinstr], f, [(*noops*)]);
      (Lw   (minCalleeReg + 1) sp (-sz + 8),  [Tinstr], f, [(*noops*)]);
      (Lw   (minCalleeReg + 2) sp (-sz + 4),  [Tinstr], f, [(*noops*)]);
      (* proper return sequence *)
      (Addi sp sp (-sz) , [Tinstr; Tr1], f, [(Dealloc 0 sz)])
    ; (Lw   ra sp 0     , [Tinstr; Tr2], f, [(*noops*)])
    ; (Jalr ra ra 0     , [Tinstr; Tr3], f, [Return])
    ].

  Definition takeAddrSeqOfOpt (fp : FunctionProfile) (rd:Register) (a : (nat * Z))
    : list (InstructionI * TagSet * FunID * list Operation) :=
    match a with
    | (x,off) => [(Addi rd sp off, [Tinstr; Tvar x], fp.(id), [(*noops*)])]
    end.

  Definition findAddrToTake (fp : FunctionProfile) :=
    elems_ None
           (map (fun '(x,off,_) => Some (x,off))
                (filter (fun '(_,k) =>
                           match k with
                           | Lpublic => true
                           | Lsecret => false end)
                        (localsByName fp.(locals)))).
  
  Definition genTakeAddrSeq (m:MachineState) (fp : FunctionProfile)
    : G (option (list (InstructionI * TagSet * FunID * list Operation))) :=
    opt_target <- findAddrToTake fp;;
    match opt_target with
    | None => ret None
    | Some a => rd <- genTargetReg m;;
                ret (Some (takeAddrSeqOfOpt fp rd a))
    end.
    
  (* The current function's expected behavior. We use the strat like a probabilistic
     state-machine: each step we have some chance of transitioning to a different
     strat, weighted by special events such as entering a function for the first
     time or having control return to us. *)
  Inductive strat :=
  | initialize (offs : list Z)
  | compute
  | call (f:FunID)      
  | returned (f:FunID)
  | bored               (* We have been following a pre-generated control path
                           for too long. It's time to change it up by creating a
                           branch that will lead us somewhere else. *)
  | tired               
  | accomplice          (* This represents the current function being either erroneous
                           or compromised in service to an attacker. It will attempt
                           to place values with "interesting" tags in places where they
                           might be accessible later. This strategy is aware of the tagging
                           mechanism and will avoid making loads and stores that would
                           failstop. *)
  | smart_attacker      (* The counterpart to accomplice, this strategy will attempt to
                           violate the properties by loading or storing at an illegal
                           address. It is tag-aware and will search the state for
                           tags that will let it do so without a failstop. *)
  | dumb_attacker
  .

  Derive Show for strat.

  Close Scope Z.
  Open Scope nat.
(*      '(odds,aseq) <- genTakeAddrSeq m fprof;;
                   freq [(2, callHead (callee.(entry) - pcVal) f i m callee false);
                         (odds, aseq)]
              *)
  Definition strat_options (s : strat) (i : LayoutInfo) (t : TagInfo) (m : MachineState)
             (dataP codeP : TagSet -> bool) (cm : CodeMap_Impl)
             (f:FunID) (functions : list FunctionProfile) :
    G (list (InstructionI * TagSet * FunID * list Operation) * strat) :=
    let spVal := projw m (Reg SP) in
    let pcVal := projw m PC in
    let noops : list Operation := [] in
    let ofprof := find (fun fp => Nat.eqb f fp.(id)) functions in
    match s,ofprof with
    | initialize offs, Some fprof =>
        (* The current function has just been called.
           We are likely to write to our frame, but will not read it.
           We are likely to read from function arguments in memory (TODO)
           and use register arguments. *)
        match offs with
        | [] => exception "Empty init list"
        | off::offs' =>
            pick <- elems_ off offs;;
            seq <- genLocalWrite m fprof true false (Some pick);;
            ret (seq, initialize (List.remove Z.eq_dec off offs))
        end
    (* ROB: right now all we do during initialization is write from registers to locals.
       But once you have genArgRead, it would be great to also do some reads from the stack args,
       which we could then use to initialize locals in future steps.
       Heck, maybe even some multi-step sequences to copy locals! *)
    | compute, Some fprof =>
        (* We are in the bulk of execution. We will make reads and
           writes, primarily in the stack frame, as well as outside
           of the stack entirely. *)
        seq <- freq [(5, res <- genArith i t m cm f;;
                         ret [res]);
                     (5, genLocalWrite m fprof false false None);
                     (5, genLocalRead m fprof);
                     (1, genPtrWrite m fprof true);
                     (1, genPtrRead m fprof true)
                ];;
        ret (seq,compute)
    (* ROB: likewise, adding genArgRead in here. *)
    | call f', Some fprof =>
        (* We are preparing to call f. We will tend to choose f's
           arguments as destinations for operations. At some point,
           we will make the call. *)
        cseq <- match find (fun fp => Nat.eqb f' fp.(id)) functions with
               | Some callee => callHead (callee.(entry) - pcVal) f i m callee false
               | _ => exception "Couldn't find any functions"
                end;;
        opt_aseq <- genTakeAddrSeq m fprof;;
        seq <- match opt_aseq with
               | None => ret cseq
               | Some aseq => freq [(2,ret cseq);(1, ret aseq)]
               end;;
        ret (seq,call f')
    (* ROB: once you've written genArgWrite, give call _ the possibility of using that.
       This can take the place of your hard-coded argument initialization in the callHeads. *)
    | returned f', Some fprof =>
        (* We just got back from f, and are likely to use the
           return register as a source, along with any memory
           that we passed by reference. *)
        seq <- freq [(1, genLocalWrite m fprof false true None);
                     (1, genLocalRead m fprof);
                     (1, res <- genArith i t m cm f;;
                         ret [res])];;
        ret (seq, s)
    (* ROB: For functions with Public data, maybe a way to prioritize reading that data here? *)
    | tired, Some fprof =>
        (* We have been executing for a long time, and want to return.
           We are likely to choose the return register as a destination
           and to make a return. *)
        callee <- elems_ fprof functions;;
        cseq <- callHead (callee.(entry) + 8 - pcVal) f i m callee true;;
        freq [(3, ret (returnSeq f fprof, s));
              (1, ret (cseq, s))]
    | dumb_attacker, Some fprof =>
        (* After failing to find an attack for long enough, the smart
           attacker becomes a dumb attacker, which will just start trying
           things without regard to the tags. Anything goes! *)
        seq <- freq [(1,
                       let minImm := (-10)%Z in
                       let maxImm := 5%Z in
                       imm <- (genImm (maxImm - minImm));;
                       rd <- (genTargetReg m);;
                       let instr := Lw rd sp imm in
                       ret [(instr, [Tinstr], f, noops)]);
                     (1,
                       let minImm := (-10)%Z in
                       let maxImm := 5%Z in
                       imm <- (genImm (maxImm - minImm));;
                       rs <- (genTargetReg m);;
                       let instr := Sw sp rs imm in
                       ret [(instr, [Tinstr], f, noops)]);
                     (1, genPtrWrite m fprof false);
                     (1, genPtrRead m fprof false)];;
        ret (seq, s)
    | _, _ => exception "Not yet implemented"
    end.
  
  (* variantOf (fun k => fst c k = Sealed d) m n -> *)
  Definition genVariantOf (d : nat) (c : Ctx) (m : MachineState)
  : G MachineState :=
    foldGen (fun macc k =>
               (*trace (show ("Varying:", k, fst c k)) *)
               (match fst c k with
                | public =>
                  ret macc
                | _ =>
                    z <- (genImm 40);;
                    (ret (jorpw macc k z))
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

  Instance ShowStuff : Show (InstructionI * TagSet * FunID * list Operation) :=
    {| show '(i, ts, f, a) := (show i ++ "@" ++ show ts ++ "|" ++ show f)%string |}.
  
  Definition step_strat (s : strat) (functions : list FunctionProfile) (f : FunID)
             (* function /after/ the step *)
             (funSteps : list nat) (ops : list Operation) : G (strat * list nat) :=
    let or_attack s :=
      freq_ (ret s) [(99, ret s); (1, ret dumb_attacker)]
    in
    match find isCall ops with
    | Some (Call f' _ _) =>
        match find (fun fp => Nat.eqb f' fp.(id)) functions with
        | Some callee =>
            let offs := allLocalOffsets callee in
            s' <- or_attack (initialize offs);;
            ret (s', funMaxFuel::funSteps)
        | _ => exception "Couldn't find callee"
        end
    | _ =>
      match funSteps with
      | fFuel::rest =>
          match find isTailcall ops with
          | Some (Tailcall f' _ _) =>
              match find (fun fp => Nat.eqb f' fp.(id)) functions with
              | Some callee =>
                  let offs := allLocalOffsets callee in
                  s' <- or_attack (initialize offs);;
                  ret (s', funMaxFuel::rest)
              | _ => exception "Couldn't find callee"
              end
          | _ => if existsb isReturn ops
                 then s' <- or_attack (returned f);;
                      ret (s', rest) else
                   s' <-
                     match s with
                     | initialize offs =>
                         match offs with
                         | [] => ret compute
                         | _ => or_attack s
                         end
                     | compute =>
                         if fFuel <? 10 then or_attack tired else
                           s' <- freq_ (ret compute)
                                       ([(1, ret compute)] ++
                                                           map (fun fp => (if fp.(id) =? f then 1 else 2,
                                                                            ret (call fp.(id)))) functions);;
                           or_attack s'
                     | call f => ret s
                     | returned f =>
                         s' <- freq_ (ret compute) [(2, ret (returned f)); (1, ret compute)];;
                         or_attack s'
                     | bored => ret compute
                     | tired => ret tired
                     | accomplice => ret compute
                     | smart_attacker => ret compute
                     | dumb_attacker => ret tired
                     end;;
                   ret (s', (pred fFuel)::rest)
          end
      | [] => exception "funSteps should never be empty"
      end
    end.
  
  Close Scope nat.
  Open Scope Z.

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
           (li : LayoutInfo) (ti : TagInfo) (s : strat)
           (mp0 : MachineState)
           (mp  : MachineState)
           (cm : CodeMap_Impl) (f : FunID)
           (functions : list FunctionProfile)
           (its : list (InstructionI * TagSet * FunID * list Operation))
           (dataP codeP : TagSet -> bool)
    (* num calls? *)
    : G (MachineState * strat * MachineState * CodeMap_Impl) :=
    let '(m0,p0) := mp0 in
    let '(m,p) := mp in
    match steps with
    | O =>
        (* Out-of-fuel: End generation. *)
        "Out of Fuel" ! (ret (mp, s, mp0, cm))
    | S steps' =>
      match map.get (getMem m) (getPc m) with
      | Some _ =>
        match its with
        | [] =>
            (* Instruction already exists, step... *)
            let '(mp',ops,_) := step mp in
            (* ...and recurse. *)
            '(s', funSteps') <- step_strat s functions f funSteps ops;;
            (* ROB: maybe we should have some chance of setting s' to bored here?
               Not sure if it should be probabilistic, or by counting the number of
               times we've been here, or what. Probably probabilistic, more state
               is not great. *)
            gen_exec_aux steps' funSteps' li ti s' mp0 mp' cm f functions its codeP dataP
        | _ =>
          ("Existing instruction mid-sequence" ++ nl)%string !
          (ret (mp, s, mp0, cm))
        end
      | None =>
          '(it, its', s', funSteps') <-
            (* Check if there is anything left to put *)
            (match its with
             | [] =>
                 (* There isn't. Generate an instruction sequence. *)
                 '(its',s') <- strat_options s li ti mp dataP codeP cm f functions;;
                 match its' with
                 | it :: its'' =>
                     let '(_,_,_,ops) := it in
                     '(s', funSteps') <- step_strat s' functions f funSteps ops;;
                     ("Steps left: " ++ show steps ++ " Strat: " ++ show s ++ ", Pending: " ++ show its ++ ", Gen: " ++
                                     show it ++ ", " ++ show its'' ++ nl)%string !
                     ret (it, its'', s', funSteps')
                 | _ => exception "EmptyInstrSeq"
                 end
             | it::its' =>
                 let '(_,_,_,ops) := it in
                 '(s', funSteps') <- step_strat s functions f funSteps ops;;
                 ("Steps left: " ++ show steps ++ ", Pending: " ++ show its ++ ", Take: " ++ show it ++ ", Leave: " ++ show its' ++ nl)%string !
                 ret (it, its', s', funSteps')
             end);;
          let '(i,t,f',a) := it in
          let mp0' := setInstrI (getPc m) mp0 i in
          let mp'  := setInstrI (getPc m) mp  i in
          let mp0'' := setInstrTagI (word.unsigned (getPc m)) mp0' t in
          let mp''  := setInstrTagI (word.unsigned (getPc m)) mp' t in
          let cm' := map.put cm (word.unsigned (getPc m)) (Some a) in
          let '(mp''',_,_) := mpstep mp'' in
          if weq (projw mp''' PC) (projw mp PC) then
            ("Failstopped" ++ nl) ! (ret (mp''',s,mp0'',cm'))
          else
            (gen_exec_aux steps' funSteps' li ti s' mp0'' mp''' cm' f' functions its' dataP codeP)
      end
    end.

  Definition replicateGen {A} (n : nat) (g : G A) : G (list A) :=
    let fix aux n :=
        match n with
        | O => returnGen nil
        | S n' => liftGen2 cons g (aux n')
        end in
    aux n.
  
  Definition genGPRs (t : TagInfo) (mp : MachineState) : G MachineState :=
    let (m,p) := mp in
    (* first block for argument registers *)
    ds <- (replicateGen 3 (genImm 40));;
    ts <- (replicateGen 3 (returnGen (regTag t)));;
    let regs :=
      List.fold_left (fun '(i,m) r =>
                        (i+1, map.put m i (word.of_Z r)))
                     ds (minReg, getRegs m) in
    let tags : Z * TagMap :=
      List.fold_left (fun '(i,m) (t : TagSet) =>
                        (i+1, map.put m i t))
                     ts (minReg, regtags p) in
    (* second block for callee-save registers (TODO refactor) *)
    ds <- (replicateGen 3 (genImm 40));;
    ts <- (replicateGen 3 (returnGen (regTag t)));;
    let regs' :=
      List.fold_left (fun '(i,m) r =>
                        (i+1, map.put m i (word.of_Z r)))
                     ds (minCalleeReg, (snd regs)) in
    let tags' : Z * TagMap :=
      List.fold_left (fun '(i,m) (t : TagSet) =>
                        (i+1, map.put m i t))
                     ts (minCalleeReg, (snd tags)) in
    (* generator *)
    ret (withRegs (snd regs') m,
          p <| regtags := snd tags' |>).
  
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
             (dataP codeP : TagSet -> bool)
    : G (MachineState * CodeMap_Impl) :=
    mps <- (genDataMemory i t mp0);;
    mps' <- (genGPRs t mps);;
    '(m', fps, cm0) <- genFuns 5 mps';;
    '(m_post, s, m'', cm) <- (gen_exec_aux maxFuel [maxFuel] i t (initialize (allLocalOffsets main)) m' m' cm0 O fps
                                        [] dataP codeP);;
    (show s ++ nl ++ show (m_post,cm)) ! ret (m'',cm).

  Definition zeroedRiscvMachine : RiscvMachine := {|
    getRegs :=
      List.fold_right (fun '(i,v) m => map.put m i (word.of_Z v))
                      map.empty
                      ([ (0, 0)
                         ; (1, 0)   (* ra *)
                         ; (2, defLayoutInfo.(stackLo)) (* sp *)
                      ]);
    getPc := ZToReg 0;
    getNextPc := ZToReg 4;
    getMem := unchecked_store_byte_list
                (word.of_Z defLayoutInfo.(stackLo))
                (Z32s_to_bytes (repeat 0 125)) (* FIXME? revised default layout *)
                map.empty;
    (*unchecked_store_byte_list (word.of_Z 500)
      (Z32s_to_bytes (cons 0 nil))
      (map.empty); *)
    getXAddrs := nil; 
    getLog := nil;
                                                |}.

  Definition zeroedPolicyState : PolicyState :=
    {| nextid := 0
       ; pctags := [Tpc 0; Th1]
       ; regtags :=
           List.fold_right (fun '(i,v) m => map.put m i v)
                           map.empty
                           ([ (0, [])
                              ; (1, [Trai])   (* ra *)
                              ; (2, [Tsp]) (* sp *)
                           ])
       ; memtags :=
           (map.put 
              (snd (List.fold_right (fun x '(i,m) => (i+4, map.put m i x)) (defLayoutInfo.(stackLo), map.empty)
                                    (repeat nil 125)))
              defLayoutInfo.(stackLo)
              ([Tstack 0 Knormal]))
             (*map.empty (* map.put map.empty 500 (cons Tsp nil) *)*)
    |}.
  
  Definition genMach :=
  let codeP := fun tt => true in
  let dataP := fun tt => true in
  m <- genMachine defLayoutInfo defTagInfo (zeroedRiscvMachine,zeroedPolicyState)
                  dataP codeP;;
  (ret m).

  (* Constant generator for explicit program listings. These follow the same
     conventions as the initial machine: reserved registers (zero, RA, SP) and
     memory layout (instructions in 0-496 range, reserved space for stack etc.
     starting at 500). *)

  Definition ex_gen
    (mem : list (Z * InstructionI * TagSet * option (list Operation)))
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

  (* Counterexample to prop_laziestIntegrity', use this generator instead of the
     random machine execution generator to reproduce *)
  Definition cex01 : G (MachineState * CodeMap_Impl) :=
    ex_gen
      [(  0, Addi 2 2 12,  [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (  4, Sw 2 0 (-8),  [Tinstr],        Some [] );
       (  8, Jal 1 60,     [Tinstr; Tcall], Some [(Call O [] [])] );
       ( 68, Sw 2 1 0,     [Tinstr; Th1],   Some [] );
       ( 72, Addi 2 2 12,  [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 76, Sw 2 10 (-8), [Tinstr],        Some [] );
       ( 80, Lw 10 2 (-4), [Tinstr],        Some [] )]
      [(  8, 12, [] );
       (  9,  0, [] );
       ( 10,  4, [] )].

  Definition cex02 : G (MachineState * CodeMap_Impl) :=
    ex_gen
      [(* main *)
       (   0, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (   4, Addi 10 0 1,    [Tinstr],        Some [] ); (* Set flag to true *)
       (   8, Jal 1 92,       [Tinstr; Tcall], Some [(Call O [] [])] );
       (  12, Addi 10 0 0,    [Tinstr],        Some [] ); (* Set flag to false *)
       (  16, Jal 1 84,       [Tinstr; Tcall], Some [(Call O [] [])] );
       (* f *)
       ( 100, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 104, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 108, Beq 10 0 12,    [Tinstr],        Some [] ); (* check flag in r10 *)
       ( 112, Addi 8 0 42,    [Tinstr],        Some [] ); (* if true then store 42...*)
       ( 116, Sw 2 8 (-4),    [Tinstr],        Some [] ); (* ... into our frame *)
       ( 120, Lw 8 2 (-4),    [Tinstr],        Some [] ); (* either way, use/reuse; machine gets stuck here (2nd pass) *)
       ( 124, Sw 2 8 (-8),    [Tinstr],        Some [] );
       ( 128, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 132, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 136, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] )]
      [(  8, 12, [] );
       (  9,  0, [] );
       ( 10,  4, [] )].

  Definition cex03 : G (MachineState * CodeMap_Impl) :=
    ex_gen
      [(* main *)
       (   0, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (   4, Jal 1 72,       [Tinstr; Tcall], Some [(Call O [] [])] );
       (   8, Addi 8 8 740,   [Tinstr],        Some [] );
       (  12, Jal 1 64,       [Tinstr; Tcall], Some [(Call O [] [])] ); (* could correct this offset to 64, the same problem occurs *)
       (  16, Beq 0 0 0,      [Tinstr],        Some [] ); (* All done, now loop *)
       (* f *)
       (  76, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       (  80, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (  84, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       (  88, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       (  92, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] )] (* variant machine can step on first return, but state is not updated and becomes unsynced *)
      [(  8, 12, [] );
       (  9, 32, [] );
       ( 10, 20, [] )].

  Definition cex04 : G (MachineState * CodeMap_Impl) :=
    ex_gen
      [(* main *)
       (   0, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       (   4, Jal 1 416,      [Tinstr; Tcall], Some [(Call 1%nat [] [])] );
       (   8, Sw 2 0 (-4),    [Tinstr],        Some [] );
       (  12, Sw 2 10 (-4),   [Tinstr],        Some [] );
       (  16, Jal 1 332,      [Tinstr; Tcall], Some [(Call 2%nat [] [])] );
       (  20, Beq 0 0 0,      [Tinstr],        Some [] ); (* TODO check *)
       (* NOTE The presence of f2 and the position of f1 have no effect on this
          error, but the existence of call hierarchy does to some degree (other
          modifications, e.g., the replacement of some of the calls, lead to
          other, but different violations) -- observe that variant generation
          also mutates the hardwired zero register *)
       (* f2 *)
       ( 348, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 352, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 356, Jal 1 20,       [Tinstr; Tcall], Some [(Call 4%nat [] [])] );
       (* ( 356, Jal 1 20,       [Tinstr; Tcall], Some [(Call 4%nat [] [])] ); *)
       ( 360, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 364, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 368, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f4 *)
       ( 376, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 380, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 384, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 388, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 392, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f1 *)
       ( 420, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 424, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 428, Jal 1 20,       [Tinstr; Tcall], Some [(Call 5%nat [] [])] );
       ( 432, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 436, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 440, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] );
       (* f5 *)
       ( 448, Sw 2 1 0,       [Tinstr; Th1],   Some [] ); (* header *)
       ( 452, Addi 2 2 12,    [Tinstr; Th2],   Some [(Alloc 0 12)] );
       ( 456, Addi 2 2 (-12), [Tinstr; Tr1],   Some [(Dealloc 0 12)] ); (* footer *)
       ( 460, Lw 1 2 0,       [Tinstr; Tr2],   Some [] );
       ( 464, Jalr 1 1 0,     [Tinstr; Tr3],   Some [Return] )]
      [(  8, 12, [] );
       (  9, 28, [] );
       ( 10, 12, [] )].


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
  
End GenRISCVLazyOrig.
