From StackSafety Require Import MachineModule PolicyModule TestingModules RISCVMachine Lazy.

Import ZArith. Open Scope Z.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.Interface.

Module DefaultLayout (M:Machine) <: LayoutInfo M.
  Module PM := Properties M.
  Import PM.
  Import M.
  
  Record myLayoutInfo := { instLo : Z
                         ; instHi : Z
                         ; dataLo : Z
                         ; dataHi : Z
                         ; stackLo  : Z
                         ; stackHi  : Z                                    
                         }.

  Definition LayoutInfo := myLayoutInfo.

  Definition defLayoutInfo :=
    {| dataLo := 1000
     ; dataHi := 1020
     ; instLo := 0
     ; instHi := 499
     ; stackLo  := 500
     ; stackHi  := 600
    |}.

  Definition initCtx : Ctx :=
    let V := (fun k =>
                match k with
                | PC => public
                | Reg r => if callee_save r then sealed else free
                | Mem a => if andb (wle (ztow defLayoutInfo.(stackLo)) a) (wlt a (ztow (defLayoutInfo.(stackHi))))
                           then free
                           else public
                end) in
    (V, nil).
                    
  Definition defStackMap (i : LayoutInfo) (a : Addr) : option StackID :=
    if (andb (wle (ztow (stackLo i)) a)
             (wle a (ztow (stackHi i))))
    then
      Some O
    else None.

  Definition CodeMap_Impl : Type := Zkeyed_map (option Operations).
  Definition CodeMap_fromImpl (cm : CodeMap_Impl) : CodeMap :=
    fun addr => match map.get cm (wtoz addr) with
                | Some cs => cs
                | _ => None
                end.
End DefaultLayout.

Module RISCVDef := DefaultLayout RISCVLazyOrig.
