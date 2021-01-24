Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Trace.
Require Import Machine.
Require Import ObsTrace.

Section WITH_CONTEXT.

  Variable context : Type.
  Variable updateC : MachineState -> context -> context.

  Definition TraceIntegrityEager (K : Component -> Prop) (MCP:MCPTrace) : Prop :=
    forall k (mcp':@MCPState context),
      K k->
      Last MCP mcp' ->
      mstate (head MCP) k = mstate mcp' k.
  
  Definition variantOf (K : Component -> Prop) (m n : MachineState) :=
    forall k, ~ K k -> m k = n k.

  Definition sameDifference (m m' n n' : MachineState) :=
    forall k,
      (m k <> m' k \/ n k <> n' k) ->
      m' k = n' k.

  Definition FindSegmentMP P mp c MCP :=
    exists MCP',
      WithContextMP updateC c (MPTraceOf mp) MCP' /\
      ContextSegment P MCP' MCP.

  Definition FindSegmentM P m c MC :=
    exists MC',
      WithContextM updateC c (MTraceOf m) MC' /\
      ContextSegmentM P MC' MC.
  
  Definition TraceConfidentialityEager
             (K : Component -> Prop)
             (P:MachineState -> context -> Prop)
             (MCP:@MCPTrace context) : Prop :=
    forall MCP MO m c p n N NO,
      head MCP = (m,c,p) ->
      variantOf K m n ->
      FindSegmentM P n c N ->
      ObsOfMCP MCP MO ->
      ObsOfMC N NO ->
      (* Case 1 *)
      (forall mend dmend pend,
          Last MCP (mend,dmend,pend) ->
          ~ P mend c ->
          exists nend dnend,
            Last N (nend,dnend) /\
            ObsOfMP MO ~=_O ObsOfM NO /\
            sameDifference m mend n nend)
    /\ (* Case 2 *)
    (Infinite MCP ->
     ObsOfMP MO ~=_O ObsOfM NO)
    /\ (* Case 3 *)
    (forall mend dmend pend,
        Last MCP (mend, dmend, pend) ->
        P mend c ->
        ObsOfMP MO <=_O ObsOfM NO).

End WITH_CONTEXT.

Arguments FindSegmentMP {_} _ _ _ _ _.
Arguments TraceIntegrityEager {_} _ _.
Arguments TraceConfidentialityEager {_} _ _ _ _.
