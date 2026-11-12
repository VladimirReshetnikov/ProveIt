# Residue-90 graph-to-X model source draft

This packet proposes to supply the exact literal-graph main norm to the
[separate X=0 arithmetic draft](../ordinary13-residue90-xzero-model-draft/).
All Lean sources and inherited dependencies are **unelaborated**. Neither
this packet nor its finite controls constitute an iPRA theorem.

The source defines the graph's signed `rankRing`, `shiftRing` and `mainRoot`
from a natural port tuple. It proposes deriving, from residual 1 of the exact
90-row graph and for arbitrary gamma,

```
Dstar² = U²*(1+(H+a²)*c²),
Dstar  = U*(X+a*c) + H*(U*gamma + X*Y*q + R + 1-k).
```

The rank here is signed, so this step assumes neither `C>0` nor any rank
window. When X is zero, `a=Y`, and those identities have exactly the
hypotheses of the separate `xzero_impossible` model-arithmetic draft. The
proposed `X_positive` additionally takes `J>0` and positive represented beta
to obtain `q≥2` and `Y≥q³`; it does not assume gamma positive or a root sign.

The symbolic compact client composes the proposed J-forcing, X-forcing,
first-norm C-gap, rank-window, natural quotient and gamma clients. Its K is
still an **arbitrary standard natural**. This is source-level composition,
not a checked proof: the 90/91 mixed-shift zero maps, authenticated fixed
kernel/port byte binding, provider ancestry, physical displayed equation and
internal iPRA endpoint remain outside this packet.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-xzero-graph-draft/check.py | cmp - research/ordinary13-residue90-xzero-graph-draft/receipt.json
```

The read-only checker pins the graph and inherited draft sources, reruns
their deterministic checks, and tests the two displayed exact identities on
bounded natural tuples. It does not run Lean, validate nonstandard-model
reasoning, stage artifacts or authenticate compiled providers.
