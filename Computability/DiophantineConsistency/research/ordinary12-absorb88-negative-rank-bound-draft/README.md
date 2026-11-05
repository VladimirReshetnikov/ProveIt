# Signed rank bound on the 88 negative-transport branch

The checked theorem `graph_rank_lower` applies in the indicated models of
IΣ₁ to a positive actual 88-graph zero with `beta>0`. Put

```
b=J*beta, q=1+b, X=q*w, Y=q³*s, P=XY²,
A=K0+w, Bp=q*A, Bn=(F+alpha)*A+F,
G=alpha+b*(q-F), rank=(q²-1)*G+J*(MC+MF*q),
```

where subtractions and the rank are interpreted in the model difference
ring. Under the **additional** negative-transport hypothesis `ιBp < ιBn`,
the theorem proves `−q²P ≤ rank`. It combines the checked actual-graph
transport magnitude bound `q*(Bn−Bp)≤P` with a generic ordered-ring rank
lemma. When `G<0`, positivity forces `F>q`, which in turn makes
`−G < bF < qF < q*(Bn−Bp)≤P`; when `G≥0`, `G+P≥0` is immediate.
Nonnegativity of the remaining rank contribution yields the result.

This is a lower bound, not a proof of nonnegative rank, transport positivity,
positive main root, 88/89 reverse existence, or an iPRA endpoint.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0. Both the generic and graph-specific
theorems reported axioms `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`. Lean warned that `hF` was not explicitly referenced in the generic
lemma; it remains an explicit premise and is available to arithmetic tactics.
From the repository root, after building the prior graph-bound object:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-divisibility-draft/observations/attempt02/terminal.json"))["lean_path"])')
LEAN_PATH=/tmp:$TASK_LEAN_PATH /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-rank-bound-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-negative-rank-bound-draft/Absorb88NegativeRankBound.lean \
  -o /tmp/Absorb88NegativeRankBound.olean
```

Source SHA-256:
`36563548a7dae1bf2b4188cf5ef27127548cb1afb62073914a202d1951b971c1`;
result SHA-256:
`7e51595186792e27e68bc9bea5b5b34fe87f01328d723f085d7c40e613c414be`.
The direct graph-bound object SHA-256 was
`a563cc4dee46729fb096917af85145df04bf10daa144c4a937189152d29ea40e`.
The temporary provider chain, including its full project, package, dynamic,
and search-path ancestry, was inherited and not independently audited.
