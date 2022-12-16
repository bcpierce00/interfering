Require Coq.Strings.String. Open Scope string_scope.
From StackSafety Require Import MachineModule PolicyModule TestingModules
     RISCVMachine DefaultLayout Lazy.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Import ZArith. Open Scope Z.
Require Import coqutil.Word.Interface.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.Interface.
Require Import Coq.Lists.List. Import ListNotations.

(*Module PrintRISCVLazyFixed : Printing RISCV TPLazyFixed DLObs TSSRiscvDefault.
  Module MPC := TestMPC RISCVObs TPLazyFixed DLObs TSSRiscvDefault.
  Import MPC.

  Definition printObsType (o:Event) := "".
  Instance ShowObsType : Show Event :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Definition printPC (m : MachineState) (p : PolicyState) :=
  (show (projw m PC) ++ " @ " ++ show (pctags p))%string.

  Definition printPCs (m n : MachineState) (p : PolicyState) :=
    let val1 := projw m PC in
    let val2 := projw n PC in
    ((if Z.eqb val1 val2 then
        show val1
      else (show val1 ++ "/" ++ show val2))
       ++ " @ " ++ show (pctags p))%string.

  (* NOTE Reusing old name for now (but annotations are lists of operations) *)
  Instance ShowCodeAnnotation : Show Operation :=
    {| show ca :=
         match ca with
         | Call _ _ _ => "Call"
         | Tailcall _ _ _ => "Tailcall"
         | Return => "Return"
         | Alloc _ _ => "Alloc"
         | Dealloc _ _ => "Dealloc"
         end |}.

  Derive Show for StackDomain.
  
  Definition printComponent (k : Element)
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
      else combine_match l1' l2' (*exception ("combine_match - not_eq " ++ (show (l1, l2))%string)*)
    | nil, nil => nil
    | _, _ => nil (*exception ("combine_match: " ++ (show (l1,l2)))%string*)
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

  Derive Show for Element.

  Instance ShowValue : Show Value :=
    {| show v := show v |}.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
    {| show := fun '(m,p,cm) => printMachine m p cm (initCtx defLayoutInfo) |}.

End PrintRISCVLazyFixed.*)

Module PrintRISCVLazyOrig : Printing RISCVLazyOrig RISCVDef.
  Import RISCVLazyOrig.
  Import TagPolicyLazyOrig.
  Import RISCVDef.
  Import PM.

  Definition printObsType (o:Event) := "".
  Instance ShowObsType : Show Event :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Definition printPC (m : MachineState) :=
    let (w,t) := proj m PC in
    (show w ++ " @ " ++ show t)%string.

  Definition printPCs (m n : MachineState) :=
    let val1 := projw m PC in
    let val2 := projw n PC in
    ((if Z.eqb val1 val2 then
        show val1
      else (show val1 ++ "/" ++ show val2))
       ++ " @ " ++ show (pctags (snd m)))%string. (* v. n-tags? *)

  (* NOTE Reusing old name for now (but annotations are lists of operations) *)
  Instance ShowCodeAnnotation : Show Operation :=
    {| show ca :=
         match ca with
         | Call _ _ _ => "Call"
         | Tailcall _ _ _ => "Tailcall"
         | Return => "Return"
         | Alloc _ _ => "Alloc"
         | Dealloc _ _ => "Dealloc"
         end |}.

  Derive Show for Sec.
  
  Definition printComponent (k : Element)
           (m : MachineState)
           (cm : CodeMap_Impl) (c : Ctx)
           (i : LayoutInfo) :=
  let (val,tag) := proj m k in
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
  | PC => ("PC: " ++ printPC m ++ " - " ++
      match decode RV32I (projw m (Mem val)) with
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
      else combine_match l1' l2' (*exception ("combine_match - not_eq " ++ (show (l1, l2))%string)*)
    | nil, nil => nil
    | _, _ => nil (*exception ("combine_match: " ++ (show (l1,l2)))%string*)
    end.

  Definition listify2 {A B} `{Show A} `{Show B}
             (m1 : Zkeyed_map A)
             (m2 : Zkeyed_map B) : list (Z * A * B) :=
    combine_match (listify1 m1) (listify1 m2).

  Definition printGPRs (mp : MachineState) :=
    let '(m,p) := mp in
    List.fold_left (fun acc '(rID, rVal, rTag) =>
                      show rID ++ " : " ++ show rVal ++ " @ " ++ show rTag ++ nl ++ acc)%string 
                   (listify2 (RiscvMachine.getRegs m) (regtags p)) "".

  Definition printGPRss (m n : MachineState) :=
    let '(ms, mp) := m in
    let '(ns, _) := n in (* v. n-tags? *)
    let regs1 := listify2 (getRegs ms) (regtags mp) in
    let regs2 := listify2 (getRegs ms) (regtags mp) in
    List.fold_left
      (fun acc '((rID1, rVal1, rTag1),(rID2, rVal2, rTag2)) =>
         if andb (Z.eqb rID1 rID2) (TagSet_eqb rTag1 rTag2)
         then
           ("r" ++ show rID1 ++ " : " ++
           (if Z.eqb (word.unsigned rVal1) (word.unsigned rVal2) then show rVal1
             else (show rVal1 ++ "/" ++ show rVal2))
              ++ " @ " ++ show rTag1 ++ nl ++ acc)%string
         else
           exception "printGPRss - unequal rID/rTag"
      ) (List.combine regs1 regs2) "".

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

  Definition printMem (mp : MachineState) (cm : CodeMap_Impl) (c : Ctx) (i : LayoutInfo) :=
    let (m,p) := mp in
    let mem := RiscvMachine.getMem m in
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

  Definition printMems (m n : MachineState) (cm : CodeMap_Impl) (c : Ctx) (i : LayoutInfo) :=
    let tags := memtags (snd m) in (* v. n-tags? *)
    let mem1 := getMem (fst m) in
    let mts1 := combine_match (listify1_word mem1) (listify1 tags) in
    let mem2  := getMem (fst n) in
    let mts2  := combine_match (listify1_word mem2) (listify1 tags) in

    List.fold_left
      (fun s '((k1,val1,t1),(k2,val2,t2)) =>
         if andb (Z.eqb k1 k2) (TagSet_eqb t1 t2) then
         let printed :=
             if andb (Z.leb (instLo i) k1)
                     (Z.leb k1 (instHi i))
             then
               if Z.eqb val1 val2 then
               match decode RV32I val1 with
               | IInstruction inst =>
                 (show inst ++ " @ " ++ show t1 ++ " < " ++ show (CodeMap_fromImpl cm k1) ++ " > - " ++ show (fst c (Mem k1)))%string
               | _ => (show val1 ++ " <not-inst>")%string
               end
               else exception "Instructions not equal"
             else
               let printVar :=
                   (if Z.eqb val1 val2 then
                      show val1
                    else (show val1 ++ "/" ++ show val2))%string in
               (printVar ++ " @" ++ show t1 ++ " < " ++ show (CodeMap_fromImpl cm k1) ++ " > - " ++ show (fst c (Mem k1)))%string in
         if andb (andb (Z.eqb val1 0) (Z.eqb val2 0)) (seq.nilp t1) then
           s
         else
           ("[" ++ show k1 ++ "]: " ++ printed ++ nl ++ s)%string
         else exception "printMems - not equal k/t"
      ) (List.combine mts1 mts2) "".

  Definition printMachine (m : MachineState) cm c :=
    (
      "PC:" ++  
      printPC m ++ nl ++
      "Registers:" ++ nl ++
      printGPRs m ++ nl ++
      "Memory: " ++ nl ++
      printMem m cm c defLayoutInfo ++ nl
    )%string.

  Definition printMachines
             (m n : MachineState) cm c := (
    "PC:" ++
    printPCs m n ++ nl ++
    "Registers:" ++ nl ++
    printGPRss m n ++ nl ++
    "Memory: " ++ nl ++
    printMems m n cm c defLayoutInfo ++ nl
    )%string.

  Derive Show for Element.

(*  Instance ShowValue : Show Value :=
    {| show v := show v |}.*)
  
  Instance ShowM : Show (MachineState * CodeMap_Impl):=
    {| show := fun '(m,cm) => printMachine m cm initCtx |}.

End PrintRISCVLazyOrig.

(*Module PrintRISCVLazyNoCheck : Printing RISCVObs TPLazyNoCheck DLObs TSSRiscvDefault.
  Module MPC := TestMPC RISCVObs TPLazyNoCheck DLObs TSSRiscvDefault.
  Import MPC.

  Definition printObsType (o:Event) := "".
  Instance ShowObsType : Show Event :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Definition printPC (m : MachineState) (p : PolicyState) :=
  (show (projw m PC) ++ " @ " ++ show (pctags p))%string.

  Definition printPCs (m n : MachineState) (p : PolicyState) :=
    let val1 := projw m PC in
    let val2 := projw n PC in
    ((if Z.eqb val1 val2 then
        show val1
      else (show val1 ++ "/" ++ show val2))
       ++ " @ " ++ show (pctags p))%string.

  (* NOTE Reusing old name for now (but annotations are lists of operations) *)
  Instance ShowCodeAnnotation : Show Operation :=
    {| show ca :=
         match ca with
         | Call _ _ _ => "Call"
         | Tailcall _ _ _ => "Tailcall"
         | Return => "Return"
         | Alloc _ _ => "Alloc"
         | Dealloc _ _ => "Dealloc"
         end |}.

  Derive Show for StackDomain.
  
  Definition printComponent (k : Element)
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
      else combine_match l1' l2' (*exception ("combine_match - not_eq " ++ (show (l1, l2))%string)*)
    | nil, nil => nil
    | _, _ => nil (*exception ("combine_match: " ++ (show (l1,l2)))%string*)
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

  Derive Show for Element.

  Instance ShowValue : Show Value :=
    {| show v := show v |}.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
    {| show := fun '(m,p,cm) => printMachine m p cm (initCtx defLayoutInfo) |}.

End PrintRISCVLazyNoCheck.

Module PrintRISCVLazyNoDepth : Printing RISCVObs TPLazyNoDepth DLObs TSSRiscvDefault.
  Module MPC := TestMPC RISCVObs TPLazyNoDepth DLObs TSSRiscvDefault.
  Import MPC.

  Definition printObsType (o:Event) := "".
  Instance ShowObsType : Show Event :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Definition printPC (m : MachineState) (p : PolicyState) :=
  (show (projw m PC) ++ " @ " ++ show (pctags p))%string.

  Definition printPCs (m n : MachineState) (p : PolicyState) :=
    let val1 := projw m PC in
    let val2 := projw n PC in
    ((if Z.eqb val1 val2 then
        show val1
      else (show val1 ++ "/" ++ show val2))
       ++ " @ " ++ show (pctags p))%string.

  (* NOTE Reusing old name for now (but annotations are lists of operations) *)
  Instance ShowCodeAnnotation : Show Operation :=
    {| show ca :=
         match ca with
         | Call _ _ _ => "Call"
         | Tailcall _ _ _ => "Tailcall"
         | Return => "Return"
         | Alloc _ _ => "Alloc"
         | Dealloc _ _ => "Dealloc"
         end |}.

  Derive Show for StackDomain.
  
  Definition printComponent (k : Element)
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
      else combine_match l1' l2' (*exception ("combine_match - not_eq " ++ (show (l1, l2))%string)*)
    | nil, nil => nil
    | _, _ => nil (*exception ("combine_match: " ++ (show (l1,l2)))%string*)
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

  Derive Show for Element.

  Instance ShowValue : Show Value :=
    {| show v := show v |}.

  Instance ShowMP : Show (MachineState * PolicyState * CodeMap_Impl):=
    {| show := fun '(m,p,cm) => printMachine m p cm (initCtx defLayoutInfo) |}.

End PrintRISCVLazyNoDepth.
*)
