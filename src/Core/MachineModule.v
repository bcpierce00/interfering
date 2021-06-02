Module Type Machine.

(*  Axiom exception : forall {A}, string -> A.
  Extract Constant exception =>
  "(fun l ->
         let s = Bytes.create (List.length l) in
          let rec copy i = function
          | [] -> s
          | c :: l -> Bytes.set s i c; copy (i+1) l
          in failwith (""Exception: "" ^ Bytes.to_string (copy 0 l)))". *)


  Parameter Word : Type.
  Parameter Addr : Type.
  Parameter Value : Type.

  Parameter wtoa : Word -> option Addr.
  Parameter vtow : Value -> Word.
  
  Parameter wlt : Word -> Word -> bool.
  Parameter alt : Addr -> Addr -> bool.

  Parameter weq : Word -> Word -> bool.
  Parameter aeq : Addr -> Addr -> bool.

  Parameter WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.
  Parameter AddrEqDec : forall (a1 a2 : Addr), {a1 = a2} + {a1 <> a2}.

  Parameter weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.
  Parameter aeq_implies_eq :
    forall a1 a2,
      aeq a1 a2 = true -> a1 = a2.

  Parameter not_aeq_implies_neq :
    forall a1 a2,
      aeq a1 a2 = false -> a1 <> a2.

  Parameter wle : Word -> Word -> bool.
  Parameter ale : Addr -> Addr -> bool.
  
  Parameter wplus : Word -> nat -> Word.
  Parameter aplus : Addr -> nat -> Addr.

  Parameter wminus : Word -> nat -> Word.
  Parameter aminus : Addr -> nat -> Addr.
  
  Parameter wplus_neq : forall w (n : nat),
      (n > O)%nat -> w <> wplus w n.

  Parameter Register : Type.

  Parameter RA : Register.
  Parameter SP : Register.
  Parameter regEq : Register -> Register -> bool.
  
  Inductive Component:=
  | Mem (a:Addr)
  | Reg (r:Register)
  | PC.

  Parameter keqb : Component -> Component -> bool.

  Parameter MachineState : Type.
  Definition View := Component -> Value.

  Parameter proj : MachineState -> Component -> Value.
  Parameter projw : MachineState -> Component -> Word.

  Parameter proj_vtow : forall m k, vtow (proj m k) = projw m k.

  (* Maybe name this pullback instead *)
  Parameter jorp : MachineState -> Component -> Value -> MachineState.
  
  Parameter getComponents : MachineState -> list Component.
  
  (* Observations are ObsType, or silent (tau) *)
  Parameter ObsType : Type.
  
  Inductive Observation : Type := 
  | Out (o:ObsType) 
  | Tau. 

  Parameter obs_eqb : Observation -> Observation -> bool.

  (* A Machine State can step to a new Machine State plus an Observation. *)
  Parameter step : MachineState -> MachineState * Observation.

  Parameter FunID : Type.
  Parameter StackID : Type.

  (*Definition EntryMap := Addr -> bool.*)

  Definition StackMap := Addr -> option StackID.

  Inductive CodeAnnotation : Type :=
  | call
  | retrn
  | yield
  | scall (f: MachineState -> Addr -> bool)
  | normal
  .

(*  Inductive CodeStatus :=
  | inFun   : FunID -> CodeAnnotation -> CodeStatus
  | notCode : CodeStatus
  .*)
  
  Definition CodeMap := Addr -> option CodeAnnotation.

  Parameter activeStack : StackMap -> MachineState -> option StackID.
   
  Parameter stack_eqb : StackID -> StackID -> bool.

  Parameter optstack_eqb : option StackID -> option StackID -> bool.

  Parameter justRet : MachineState -> MachineState -> Prop.

  Parameter justRet_dec : forall mc m, {justRet mc m} + {~ justRet mc m}.
End Machine.
