# Negative transport bound for an 88 graph zero

`graph_negative_transport_bound` binds the generic bound in the sibling
`ordinary12-absorb88-negative-transport-bound` packet to an actual 88-graph
zero in the model represented in the source. Write `b=J*beta`, `q=1+b`,
`X=q*w`, `Y=q³*s`, `P=(X*Y)*Y`, `A=K0+w`, `Bp=q*A`, and
`Bn=(F+alpha)*A+F`. Given positive `beta` in the model, all 12 input variables
positive, and the graph output equal to zero, the theorem shows that the
**additional hypothesis** `ιBp < ιBn` implies

```
(ιq) * (ιBn − ιBp) ≤ ιP
```

in the model difference ring. It obtains the first Pell root and the two
first-square signs from existing graph-specific lemmas, excludes one root
sign using positive `b`, `r`, and transport magnitude, and applies the
generic discrete ordered-ring bound to the other. These are Lean-level model
lemmas; the result does not show that the negative branch is impossible,
construct an 89-graph witness, establish the 88/89 reverse implication,
prove a `c/2` or `SignMod` property, or produce an iPRA endpoint.

## Observed check

The source still contains the initial `Unchecked draft` comment; the exact
source subsequently passed the check recorded here. On 2026-11-04, Lean
4.32.0 exited 0 and `#print axioms` reported `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. The check used this command from the
repository root:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-transport-graph-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-transport-graph-draft/Absorb88NegativeTransportGraph.lean \
  -o /tmp/Absorb88NegativeTransportGraph.olean
```

Source SHA-256:
`276a6248cebf7c674661f6f04216f75d68dd2570f83e6374ff47818260f87517`.
Result object SHA-256:
`a563cc4dee46729fb096917af85145df04bf10daa144c4a937189152d29ea40e`.
The directly imported generic-bound object in `/tmp` had SHA-256
`4e3a60524140a988796aaf9bbbf7967fefc43c611e484fd9024c974c4f785246`;
the `Absorb88Signs.olean` provider had SHA-256
`19111240a2efcb7fde3afa5abe93e795463aac305740e74c6f621869c67b10da`.
The terminal JSON supplying the remaining search path had SHA-256
`e78afefa6c7c679231782a9418b4529fad25e58fc01d2f5103abddb6ecd88830`.
The check inherits temporary prebuilt providers: the full project, package,
dynamic-library and search-path ancestry was not independently audited.
