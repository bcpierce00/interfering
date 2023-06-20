Require Import ZArith.
Require Import List. Import ListNotations.
Require Import Bool.
Require Import Trace.

Module Type Machine.

(*  Axiom exception : forall {A}, string -> A.
  Extract Constant exception =>
  "(fun l ->
         let s = Bytes.create (List.length l) in
          let rec copy i = function
          | [] -> s
          | c :: l -> Bytes.set s i c; copy (i+1) l
          in failwith (""Exception: "" ^ Bytes.to_string (copy 0 l)))". *)


  Parameter Value : Type.
  Parameter Word : Type.
  Definition Addr := Word.

  Parameter vtow : Value -> Word.
  Parameter ztow : Z -> Word.
  Parameter wtoz : Word -> Z.
  
  Parameter wlt : Word -> Word -> bool.

  Parameter weq : Word -> Word -> bool.

  Parameter WordEqDec : forall (w1 w2 : Word), {w1 = w2} + {w1 <> w2}.

  Parameter weq_implies_eq :
    forall w1 w2,
      weq w1 w2 = true -> w1 = w2.

  Parameter wle : Word -> Word -> bool.
  
  Parameter wplus : Word -> Z -> Word.

  Parameter wminus : Word -> Z -> Word.
  
  Parameter wplus_neq : forall w (z : Z),
      (z > 0)%Z -> w <> wplus w z.

  Parameter Register : Type.

  Parameter RA : Register.
  Parameter SP : Register.
  Parameter Reg_eq_dec : forall (r1 r2 : Register), { r1 = r2 } + { r1 <> r2 }.

  Inductive Sec :=
  | sealed
  | free
  | object
  | public
  .
  
  Parameter reg_defaults : Register -> Sec.
  Parameter RA_sealed : reg_defaults RA = sealed.
  Parameter SP_public : reg_defaults SP = public.

  Inductive Element : Type :=
  | Mem : Addr -> Element
  | Reg : Register -> Element
  | PC : Element.

  Parameter keqb : Element -> Element -> bool.

  Parameter MachineState : Type.

  Parameter proj : MachineState -> Element -> Value.
  Parameter projw : MachineState -> Element -> Word.

  (* Maybe name this pullback instead *)
  Parameter jorp : MachineState -> Element -> Value -> MachineState.
  Parameter jorpw : MachineState -> Element -> Word -> MachineState.
  
  Parameter getElements : MachineState -> list Element.
  
  (* Observations are Events, or silent (Tau) *)
  Parameter Event : Type.
  
  Inductive Observation : Type := 
  | Out (e:Event) 
  | Tau. 

  Parameter obs_eqb : Observation -> Observation -> bool.

  Parameter FunID : Type.
  Parameter Fun_eq_dec : forall (f1 f2 : FunID), { f1 = f2 } + { f1 <> f2 }.

  Definition StackID := nat.

  Definition StackMap := Addr -> option StackID.

  Inductive Operation : Type :=
  | Call (f:FunID) (reg_args:list Register) (stk_args:list (Register*Z*Z))
  | Tailcall (f:FunID) (reg_args:list Register) (stk_args:list (Register*Z*Z))
  | Return
  | Alloc (off:Z) (sz:Z)
  | Dealloc (off:Z) (sz:Z)
  .

  Lemma Op_eq_dec (op op' : Operation) :
    {op = op'} + {op <> op'}.
  Proof.
    repeat decide equality; try apply Reg_eq_dec; apply Fun_eq_dec.
  Qed.

  Definition isCall (op : Operation) : bool :=
    match op with
    | Call _ _ _ => true
    | _ => false
    end.

  Definition isTailcall (op : Operation) : bool :=
    match op with
    | Tailcall _ _ _ => true
    | _ => false
    end.

  Definition isReturn (op : Operation) : bool :=
    match op with
    | Return => true
    | _ => false
    end.
    
  (* NOTE A code map used to assign an optional annotation to an address. Now it
     assigns a optional list of operations (which can be empty!). Attention: not
     all lists are reasonable (e.g., [[Call; Return]])! We still allow unmapped
     addresses, which will be lifted to empty lists. *)
  Definition CodeMap := Addr -> option (list Operation).

  (* Stack ID of stack pointer *)
  Definition activeStack (sm: StackMap) (m: MachineState) :
    option StackID :=
    sm (projw m (Reg SP)).

  Definition stack_eqb : StackID -> StackID -> bool :=
    Nat.eqb.

  Definition optstack_eqb (o1 o2 : option StackID) : bool :=
    match o1, o2 with
    | Some n1, Some n2 => stack_eqb n1 n2
    | None, None => true
    | _, _ => false
    end.

  (* A Machine State can step to a new Machine State plus an Observation. *)
  Parameter step : MachineState -> MachineState * (list Operation) * Observation.
  
End Machine.

Module Properties (M:Machine).
  Import M.

  Definition View : Type := Element -> Sec.
  
  Definition Ctx : Type := View * list View.

  Definition State : Type := MachineState * Ctx.

  Definition in_range (m:MachineState) (a:Addr) (range:Register*Z*Z) : bool :=
    let '(r,off,sz) := range in
    wle (wplus (projw m (Reg r)) off) a &&
      wlt a (wplus (wplus (projw m (Reg r)) off) sz).    
  
  Definition arg_view (m:MachineState) (V:View) (reg_args:list Register)
             (stk_args:list (Register*Z*Z)) : View :=
                fun k => match k, V k with
                         | Reg r, _ =>
                             if existsb (fun r' => if Reg_eq_dec r r' then true else false) reg_args
                             then public
                             else reg_defaults r
                         | Mem a, object => 
                             if existsb (in_range m a) stk_args
                             then object
                             else sealed
                         | _, s => s
                         end.
  
  Definition call_op (m:MachineState) (c:Ctx) (f:FunID) (reg_args:list Register)
             (stk_args:list (Register*Z*Z)) : Ctx :=
    let '(V, σ) := c in
    let V' := arg_view m V reg_args stk_args in
    (V', V::σ).

  Definition tail_call_op (m:MachineState) (c:Ctx) (f:FunID) (reg_args:list Register)
             (stk_args:list (Register*Z*Z)) : Ctx :=
    let '(V, σ) := c in
    let V' := arg_view m V reg_args stk_args in
    (V', σ).

  Definition return_op (c:Ctx) : Ctx :=
    match c with
    | (V', V::σ) => (V, σ)
    | (V, []) => (V, [])
    end.
  
  Definition alloc_op (m:MachineState) (c:Ctx) (off sz:Z) : Ctx :=
    let '(V, σ) := c in
    let V' := fun k => match k, V k with
                       | Mem a, free =>
                           if in_range m a (SP,off,sz)
                           then object
                           else V k
                       | _, _ => V k
                       end in
    (V', σ).

  Definition dealloc_op (m:MachineState) (c:Ctx) (off sz:Z) : Ctx :=
    let '(V, σ) := c in
    let V' := fun k => match k, V k with
                       | Mem a, object =>
                           if in_range m a (SP,off,sz)
                           then free
                           else V k
                       | _, _ => V k
                       end in
    (V', σ).
  
  Definition op (m:MachineState) (c:Ctx) (ψ:Operation) : Ctx :=
    match ψ with
    | Call f reg_args stk_args => call_op m c f reg_args stk_args
    | Tailcall f reg_args stk_args => call_op m c f reg_args stk_args
    | Return => return_op c
    | Alloc off sz => alloc_op m c off sz
    | Dealloc off sz => dealloc_op m c off sz
    end.
  
  Definition cstep (s:State) := 
    let '(m,c) := s in
    let '(m',ψs,e) := step m in
    ((m', fold_left (op m) ψs c), ψs, e).

  (*** Properties of Future Returns ***)
  
  CoInductive on_return (s:State) (d:nat) (P:State -> Prop) : Prop :=
  | at_return : forall m V σ,
      s = (m, (V, σ)) ->
      length σ < d ->
      P s ->
      on_return s d P
  | future_return : forall m V σ s' ψs e,
      s = (m, (V, σ)) ->
      d <= length σ ->
      cstep s = (s', ψs, e) ->
      on_return s' d P ->
      on_return s d P
  .

  CoInductive on_both_return (s1 s2:State) (d:nat) (R:State -> State -> Prop) : Prop :=
  | at_both_return : forall m1 V1 σ1 m2 V2 σ2,
      s1 = (m1, (V1, σ1)) ->
      s2 = (m2, (V2, σ2)) ->
      length σ1 < d ->
      length σ2 < d ->
      R s1 s2 ->
      on_both_return s1 s2 d R
  | future_return_left : forall m1 V1 σ1 s1' ψs e,
      s1 = (m1, (V1, σ1)) ->
      d <= length σ1 ->
      cstep s1 = (s1', ψs, e) ->
      on_both_return s1' s2 d R ->
      on_both_return s1 s2 d R
  | future_return_right : forall m2 V2 σ2 s2' ψs e,
      s2 = (m2, (V2, σ2)) ->
      d <= length σ2 ->
      cstep s2 = (s2', ψs, e) ->
      on_both_return s1 s2' d R ->
      on_both_return s1 s2 d R
  .

  (*** Traces and Trace Generators ***)

  Definition Trace : Type := TraceOf Observation.

  CoFixpoint trace (s:State) : Trace :=
    let '(s', ψs, e) := cstep s in
    notfinished e (trace s').

  CoFixpoint trace_to_return (d:nat) (s:State) : Trace :=
    let '(m,(V,σ)) := s in
    if length σ <=? d
    then finished Tau
    else let '(s', ψs, e) := cstep s in
         notfinished e (trace_to_return d s').

  CoInductive TraceEq : Trace -> Trace -> Prop :=
  | EqTau1 : forall E1 E2,
      TraceEq E1 E2 ->
      TraceEq (notfinished Tau E1) E2
  | EqTau2 : forall E1 E2,
      TraceEq E1 E2 ->
      TraceEq E1 (notfinished Tau E2)
  | EqNow : forall e E1 E2,
      TraceEq E1 E2 ->
      TraceEq (notfinished (Out e) E1) (notfinished (Out e) E2)
  | EqAllSame : forall E,
      TraceEq E E.
  
  (*** Properties ***)

  Definition variantOf (K : Element -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> proj m k = proj n k.

  Definition irrelevant (K : Element -> Prop) (s : State) :=
    forall m c n,
      s = (m,c) ->
      variantOf K m n ->
      TraceEq (trace s) (trace (n,c)).

  Definition WBCF : Prop :=
    forall m V V' σ m' c ψs e f reg_args stk_args,
      cstep (m, (V, V'::σ)) = (m',c,ψs,e) ->
      In (Call f reg_args stk_args) ψs ->
      on_return (m',c) (length σ) (fun '(m'',_) => projw m' PC = wplus (projw m PC) 4 /\
                                                     projw m' (Reg SP) = projw m (Reg SP)).

  Definition Delta (m1 m2:MachineState) (k:Element) : Prop :=
    proj m1 k <> proj m2 k.

  Definition intersect (K1 K2: Element -> Prop) (k:Element) : Prop :=
    K1 k /\ K2 k.

  Definition union (K1 K2: Element -> Prop) (k:Element) : Prop :=
    K1 k \/ K2 k.
  
  Definition Integrity : Prop :=
    forall m c m' V σ ψs e f reg_args stk_args K P,
      cstep (m, c) = ((m',(V,σ)),ψs,e) ->
      (In (Call f reg_args stk_args) ψs \/ In (Tailcall f reg_args stk_args) ψs) ->
      K = (fun k => V k = sealed) ->
      P = (fun '(m'',c) => irrelevant (intersect K (Delta m m'')) (m'',c)) ->
      on_return (m',c) (length σ) P.

  Definition Diamond (m1 m2 n1 n2:MachineState) : Element -> Prop :=
    intersect (union (Delta m1 m2) (Delta n1 n2)) (Delta m2 n2).

  Definition CallerConfidentiality : Prop :=
    forall s m1 c1 V σ ψs e f reg_args stk_args K n1 R,
      c1 = (V,σ) ->
      cstep s = ((m1,c1),ψs,e) ->
      (In (Call f reg_args stk_args) ψs \/ In (Tailcall f reg_args stk_args) ψs) ->
      K = (fun k => V k = sealed \/ V k = free) ->
      variantOf K m1 n1 ->
      R = (fun '(m2,c2) '(n2,_) => irrelevant (Diamond m1 m2 n1 n2) (m2,c2)) ->
      on_both_return (m1,c1) (n1,c1) (length σ) R.

  Definition CalleeConfidentiality : Prop :=
    forall m c m' V σ ψs e f reg_args stk_args K P,
      cstep (m, c) = ((m',(V,σ)),ψs,e) ->
      (In (Call f reg_args stk_args) ψs \/ In (Tailcall f reg_args stk_args) ψs) ->
      K = (fun k => V k = free) ->
      P = (fun '(m'',c) => irrelevant (intersect K (Delta m m'')) (m'',c)) ->
      on_return (m',c) (length σ) P.
  
End Properties.
