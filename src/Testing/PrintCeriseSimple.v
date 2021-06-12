Require Coq.Strings.String. Open Scope string_scope.
From StackSafety Require Import MachineModule PolicyModule TestingModules
     CeriseMachine CeriseLayout TestSubroutineSimple.
From stdpp Require Import gmap fin_maps list countable.

From QuickChick Require Import QuickChick.
Import QcNotation.

Require Import ZArith. Open Scope Z.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import cap_machine.addr_reg.
Require Import machine_base.

Module PrintCeriseSimple : Printing DefCerise CerisePolicy CeriseLayout TSSCeriseDefault.
  Module MPC := TestMPC DefCerise CerisePolicy CeriseLayout TSSCeriseDefault.
  Import MPC.

  Definition printObsType (o:ObsType) := "".
  Instance ShowObsType : Show ObsType :=
    {| show o := printObsType o |}.
  Derive Show for Observation.

  Definition showAddr (a : Addr) : string :=
    match a with
    | A v _ _ => show v
    end.

  Instance ShowAddr : Show Addr :=
    {| show a := showAddr a |}.

  Definition showWord (w : Word) : string :=
    match w with
    | inl w => show w
    | inr (_,_,_,a) => show a
    end.

  Instance ShowWord : Show Word :=
    {| show w := showWord w |}.

  Definition printPC (m : MachineState) (p : PolicyState) :=
    (show (projw m PC))%string.

  Definition printPCs (m n : MachineState) (p : PolicyState) :=
    let s1 := printPC m p in
    let s2 := printPC n p in
    ((if eqb s1 s2 then
        s1
      else (s1 ++ "/" ++ s2)))%string.

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

  Definition showRegName (r:RegName) :=
    match r with
    | addr_reg.PC => "PC"
    | R n _ => ("r" ++ show n)%string
    end.

  Instance ShowRegName : Show RegName :=
    {| show r := showRegName r |}.

  Definition showZpR (v:Z + RegName) :=
    match v with
    | inl z => show z
    | inr r => show r
    end.

  Instance ShowZpR : Show (Z + RegName) :=
    {| show v := showZpR v |}.
  
  Derive Show for instr.
  
  Definition printComponent (k : Component)
           (m : MachineState) (p : PolicyState)
           (cm : CodeMap_Impl) (c : CtxState)
           (i : LayoutInfo) :=
    match k with
    | Mem a =>
      (* Check if in instruction memory *)
      if andb (Z.leb (instLo i) a) (Z.leb a (instHi i))
      then
        let val :=
            match proj m k with
            | inl z => z
            | inr (_,_,_,A z _ _) => z
            end in
        match decodeInstr val with
        | Fail => (show val ++ " <not-inst>")%string
        | inst =>
          ("[" ++ show a ++ "] : " ++ show inst ++ " < " ++ show (CodeMap_fromImpl cm a) ++ " > - " ++ show (fst c (Mem a)))%string
        end
      else
        let val := projw m k in
        ("[" ++ show a ++ "]" ++ show val ++ " < " ++ show (CodeMap_fromImpl cm a) ++ " > - " ++ show (fst c (Mem a)))%string
    | Reg r =>
      let val := projw m k in
      ("r" ++ show r ++ " : " ++ show val) %string
    | PC =>
      match proj m k with
      | inl z => "PC not cap"
      | inr (_,_,_, a) =>
        let val :=
            match proj m (Mem a) with
            | inl z => z
            | inr (_,_,_,A z _ _) => z
            end in
        match decodeInstr val with
        | Fail => ("PC: " ++ printPC m p ++ " - " ++ show val ++ " <not-inst>")%string
        | inst => ("PC: " ++ printPC m p ++ " - " ++ (show inst))%string
        end
      end
    end.

  Print map_to_list.
  
  
 (*Definition listify1 {A} {B} (m : gmap A B)
    : list (A * B) := map_to_list m.
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
    combine_match (listify1 m1) (listify1 m2). *)

  Definition printReg (rID : RegName) (rVal : Word) :=
    (show rID ++ ":" ++ show rVal ++ nl)%string.

  Definition printGenPurpRegs (m : MachineState) :=
    let '(regs, mem) := m in
    List.fold_left
      (fun acc '(rID, rVal) =>
         printReg rID rVal ++ acc)%string
      (map_to_list regs) "".

(*  Definition listify1_word mem := 
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
          else acc) nil mem).*)

  Definition printMemLoc (mAddr : Addr) (mVal : Z) (cm : CodeMap_Impl) (c : CtxState) (i : LayoutInfo) :=
    if andb (Z.leb (instLo i) (z_of mAddr))
            (Z.leb (z_of mAddr) (instHi i))
    then
      match decodeInstr mVal with
      | Fail => (show mVal ++ " <not-inst>")%string
      | inst => (show inst ++ " < " ++ show (CodeMap_fromImpl cm mAddr) ++ " > - " ++ show (fst c (Mem mAddr)))%string
      end
    else
      (show mVal ++ " < " ++ show (CodeMap_fromImpl cm mAddr) ++ " > - " ++ show (fst c (Mem mAddr)))%string.

  Definition printMem (m : MachineState) (p : PolicyState) (cm : CodeMap_Impl) (c : CtxState) (i : LayoutInfo) :=
    let mem := snd m in
    let memlist : list (Addr * Word) := map_to_list mem in
    List.fold_left
      (fun acc '(addr,val) =>
         let z := match val with
                   | inl z => z
                   | inr (_,_,_,A z _ _) => z
                   end in
         if Z.eqb z 0 then (* don't show empty memory *)
           acc
         else 
           (show addr ++ " : " ++ printMemLoc addr z cm c i ++ nl ++ acc)%string
      ) memlist "".

  
  Definition printMachine (m : MachineState) (p : PolicyState) cm c :=
    (
      "PC:" ++  
      printPC m p ++ nl ++
      "Registers:" ++ nl ++
      printGenPurpRegs m ++ nl ++
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
        if weq (projw m k) (projw m' k)
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

End PrintCeriseSimple.
