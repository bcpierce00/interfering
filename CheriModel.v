Require Import List. Import ListNotations.
Require Import Bool. Import BoolNotations.
Require Import ZArith.

Definition Word := Z.
Definition Seal := nat.

Inductive PermBit :=
| r
| w
| x
.

Definition Perm := list PermBit.

Fixpoint rP ρ :=
  match ρ with
  | r::_ => true
  | _::ρ' => rP ρ'
  | [] => false
  end.

Fixpoint xP ρ :=
  match ρ with
  | x::_ => true
  | _::ρ' => rP ρ'
  | [] => false
  end.

Fixpoint wP ρ :=
  match ρ with
  | w::_ => true
  | _::ρ' => rP ρ'
  | [] => false
  end.

Definition Cap : Type := Perm * Word * Word * Word.

Inductive Instr :=
| ld (rp rd:nat)
| ldC (rp rd:nat)
| st (rs rp:nat)
| stC (rs rp:nat)
| stU (rs rp:nat)
| stUC (rs rp:nat)
| prom (rs rd:nat)
| morp (rs rd:nat)
| seal (σ:Seal) (r1 r2:nat)
| invoke (r1 r2:nat)
.

Inductive Value :=
| v (w:Word)
| cap (c:Cap)
| ucap (c:Cap)
| scap (σ:Seal) (c:Cap)
| inst (i:Instr)
.

Definition isCap v :=
  match v with
  | cap _
  | ucap _
  | scap _ _ => true
  | _ => false
  end.

Inductive Component :=
| Reg (r:nat)
| Mem (a:Word)
| PC
.

Parameter compEqb : Component -> Component -> bool.

Definition MachineState := Component -> Value.

Definition updateMach (m:MachineState) (c:Component) (v:Value) :=
  fun c' => if compEqb c c' then v else m c.

Open Scope Z.

Definition Load (m:MachineState) (c:Cap) : option Value :=
  let '(ρ, bs, bd, o) := c in
  if rP ρ && (0 <=? o) && (o <? bd) then
    Some (m (Mem (bs + o)))
  else None.

Definition Fetch (m:MachineState) : option Instr :=
  match m PC with
  | cap (ρ, bs, bd, o) =>
    if xP ρ && (0 <=? o) && (o <? bd) then
      match (m (Mem (bs + o))) with
      | inst i => Some i
      | _ => None
      end
    else None
  | _ => None
  end.

Definition Store (m:MachineState) (c:Cap) (v:Value) : option MachineState :=
  let '(ρ, bs, bd, o) := c in
  if wP ρ && (0 <=? o) && (o <? bd) then
    Some (updateMach m (Mem (bs + o)) v)
  else None.

Definition IncCap (c:Cap) :=
  let '(ρ, bs, bd, o) := c in
  (ρ, bs, bd, o+1).

Definition Prom (u:Value) : option Value :=
  match u with
  | ucap (ρ, bs, bd, o) => Some (cap (ρ, bs, o, 0))
  | _ => None
  end.

Definition Morp (u:Value) : option Value :=
  match u with
  | ucap (ρ, bs, bd, o) => Some (ucap (ρ, o, bd-o, 0))
  | _ => None
  end.

Parameter InvokeDataReg : nat.

Inductive step : MachineState -> MachineState -> Prop :=
| ldStep : forall m rp rd c w,
    Fetch m = Some (ld rp rd) ->
    m (Reg rp) = cap c ->
    Load m c = Some (v w) ->
    step m (updateMach m (Reg rd) (v w))
| ldCStep : forall m rp rd c c',
    Fetch m = Some (ldC rp rd) ->
    m (Reg rp) = cap c ->
    Load m c = Some c' ->
    isCap c' = true ->
    step m (updateMach m (Reg rd) c')
| stStep : forall m rs rp c w m',
    Fetch m = Some (st rs rp) ->
    m (Reg rs) = v w ->
    m (Reg rp) = cap c ->
    Store m c (v w) = Some m' ->
    step m m'
| stCStep : forall m rs rp c v m',
    Fetch m = Some (stC rs rp) ->
    m (Reg rs) = v ->
    m (Reg rp) = cap c ->
    isCap v = true ->
    Store m c v = Some m' ->
    step m m'
| stUStep : forall m rs rp c c' w m',
    Fetch m = Some (stU rs rp) ->
    m (Reg rs) = v w ->
    m (Reg rp) = ucap c ->
    Store m c (v w) = Some m' ->
    IncCap c = c' ->
    step m (updateMach m' (Reg rp) (ucap c'))
| stUCStep : forall m rs rp c c' v m',
    Fetch m = Some (stUC rs rp) ->
    m (Reg rs) = v ->
    m (Reg rp) = ucap c ->
    isCap v = true ->
    Store m c v = Some m' ->
    IncCap c = c' ->
    step m (updateMach m' (Reg rp) (ucap c'))
| promStep : forall m rs rd u c,
    Fetch m = Some (prom rs rd) ->
    m (Reg rs) = u ->
    Prom u = Some c ->
    step m (updateMach m (Reg rd) c)
| morpStep : forall m rs rd u c,
    Fetch m = Some (prom rs rd) ->
    m (Reg rs) = u ->
    Morp u = Some c ->
    step m (updateMach m (Reg rd) c)
| sealStep : forall m m' m'' σ r1 r2 ccap dcap,
    Fetch m = Some (seal σ r1 r2) ->
    m (Reg r1) = cap ccap ->
    m (Reg r2) = cap dcap ->
    updateMach m (Reg r1) (scap σ ccap) = m' ->
    updateMach m' (Reg r2) (scap σ dcap) = m'' ->
    step m m''
| invokeStep : forall m m' m'' σ r1 r2 ccap dcap,
    Fetch m = Some (invoke r1 r2) ->
    r1 <> r2 ->
    m (Reg r1) = scap σ ccap ->
    m (Reg r2) = scap σ dcap ->
    updateMach m PC (cap ccap) = m' ->
    updateMach m' (Reg InvokeDataReg) (cap dcap) = m'' ->
    step m m''
.
