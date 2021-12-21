From StackSafety Require Import MachineModule PolicyModule TestingModules CeriseMachine.

Import ZArith. Open Scope Z.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.Interface.
Require Import cap_machine.addr_reg.

Module CeriseLayout <: LayoutInfo DefCerise.
  Import DefCerise.

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

  Definition defStackMap (i : LayoutInfo) (a : Addr) : option StackID :=
    if (andb (Z.leb (stackLo i) (z_of a))
             (Z.leb a (stackHi i)))
    then
      Some O
    else None.

  Definition CodeMap_Impl : Type := Zkeyed_map (option CodeAnnotation).
  Definition CodeMap_fromImpl (cm : CodeMap_Impl) : CodeMap :=
    fun addr => match map.get cm addr with
                | Some cs => cs
                | _ => None
                end.
End CeriseLayout.
