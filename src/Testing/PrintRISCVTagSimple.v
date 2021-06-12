Require Coq.Strings.String. Open Scope string_scope.
From StackSafety Require Import MachineModule PolicyModule TestingModules
     RISCVMachine DefaultLayout TestSubroutineSimple.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Import ZArith. Open Scope Z.
Require Import coqutil.Word.Interface.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.Interface.
Require Import Coq.Lists.List. Import ListNotations.

Import RiscvMachine.
Import TagPolicy.

Module PrintRISCVTagSimple : Printing RISCV TagPolicy DefaultLayout TSSRiscvDefault.
  Module MPC := TestMPC RISCV TagPolicy DefaultLayout TSSRiscvDefault.
  Import MPC.

  Definition printObsType (o:ObsType) := "".
  Instance ShowObsType : Show ObsType :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Definition printPC (m : MachineState) (p : PolicyState) :=
  (show (word.unsigned (getPc m)) ++ " @ " ++ show (pctags p))%string.

  Definition printPCs (m n : MachineState) (p : PolicyState) :=
    let val1 := word.unsigned (getPc m) in
    let val2 := word.unsigned (getPc n) in
    ((if Z.eqb val1 val2 then
        show val1
      else (show val1 ++ "/" ++ show val2))
       ++ " @ " ++ show (pctags p))%string.

  Instance ShowCodeAnnotation : Show CodeAnnotation :=
    {| show ca :=
         match ca with
         | call => "call"
         | yield => "yield"
         | scall _ => "scall"
         | normal => "normal"
         | _  => "ret"
         end |}.

  Derive Show for StackDomain.
  
  Definition printComponent (k : Component)
           (m : MachineState) (p : PolicyState)
           (cm : CodeMap_Impl) (c : CtxState)
           (i : LayoutInfo) :=
  let val := proj m k in
  let tag := pproj p k in
  match k with
  | Mem a =>
    (* Check if in instruction memory *)
    if andb (Z.leb (instLo i) a) (Z.leb a (instHi i))
    then
      match decode RV32I val with
      | IInstruction inst =>
        ("[" ++ show a ++ "] : " ++ show inst ++ " @ " ++ show tag ++ " < " ++ show (CodeMap_fromImpl cm a) ++ " > - " ++ show (fst c (Mem a)))%string
      | _ => (show val ++ " <not-inst>")%string
      end
    else
      ("[" ++ show a ++ "]" ++ show val ++ " @" ++ show tag ++ " < " ++ show (CodeMap_fromImpl cm a) ++ " > - " ++ show (fst c (Mem a)))%string
  | Reg r => 
    ("r" ++ show r ++ " : " ++ show val ++ " @ " ++ show tag) %string
  | PC => ("PC: " ++ printPC m p ++ " - " ++
      match decode RV32I (proj m (Mem val)) with
      | IInstruction inst =>
        (show inst)
      | _ => (show val ++ " <not-inst>")%string
      end)%string
  end.

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

  Definition printGPRs (m : MachineState) (p : PolicyState) :=
    List.fold_left (fun acc '(rID, rVal, rTag) =>
                      show rID ++ " : " ++ show rVal ++ " @ " ++ show rTag ++ nl ++ acc)%string 
                   (listify2 (getRegs m) (regtags p)) "". 

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

  Definition printMem (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (c : CtxState) (i : LayoutInfo) :=
    let mem := getMem m in
    let tags := memtags p in
    let mts := combine_match (listify1_word mem) (listify1 tags) in
    List.fold_left
      (fun s '(k,val,t) =>
         let printed :=
             if andb (Z.leb (instLo i) k)
                     (Z.leb k (instHi i))
             then
               match decode RV32I val with
               | IInstruction inst =>
                 (show inst ++ " @ " ++ show t ++ " < " ++ show (CodeMap_fromImpl cm k) ++ " > - " ++ show (fst c (Mem k)))%string
               | _ => (show val ++ " <not-inst>")%string
               end
             else
               (show val ++ " @" ++ show t ++ " < " ++ show (CodeMap_fromImpl cm k) ++ " > - " ++ show (fst c (Mem k)))%string in
         if andb (Z.eqb val 0) (seq.nilp t) then
           s
         else 
           (show k ++ " : " ++ printed ++ nl ++ s)%string
      ) mts "".

  
  Definition printMachine (m : MachineState) (p : PolicyState) cm c :=
    (
      "PC:" ++  
      printPC m p ++ nl ++
      "Registers:" ++ nl ++
      printGPRs m p ++ nl ++
      "Memory: " ++ nl ++
      printMem m p cm c defLayoutInfo ++ nl
    )%string.

  Derive Show for Component.

  Instance ShowValue : Show Value :=
    {| show v := show v |}.

  Fixpoint walk (ks : list Component) cm m p (c : CtxState) m' (p' : PolicyState) (c' : CtxState) (traceOut : list (unit -> string))
           (cont : unit -> Checker) : Checker :=
    match ks with
    | [] => cont tt
    | k :: ks' =>
      match fst c k with
      | Sealed _ =>
        if Z.eqb (proj m k) (proj m' k)
        then walk ks' cm m p c m' p' c' traceOut cont
        else whenFail ("Initial Machine:" ++ nl ++
                                          concatStr (List.rev (List.map (fun f => f tt) traceOut)) ++
                                          "Integrity failure at component: " ++ show k ++ nl ++
                                          "Component values: " ++ show (proj m k) ++ " vs " ++ show (proj m' k) ++ nl ++
                                          "Final state: " ++ nl ++
                                          printMachine m p cm c)%string false
      | _ => walk ks' cm m p c m' p' c' traceOut cont
      end
    end.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
    {| show := fun '(m,p,cm) => "" (*printMachine m p cm (initC (defstackmap defLayoutInfo) m) *) |}.

End PrintRISCVTagSimple.
