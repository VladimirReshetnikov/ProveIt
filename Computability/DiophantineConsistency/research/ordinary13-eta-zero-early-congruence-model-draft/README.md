# Eta-natural carrier: conditional early congruence

This is an **unelaborated source-only fact-level draft**, not a graph-zero
extraction, eta-zero impossibility proof, or iPRA endpoint. It addresses the
specific algebraic gap identified in the graph adapter audit without using
`P72Early.early` or assuming `q=3*t+2`.

For model naturals, assume `q>0`, `Y=q³*s`, and the actual prototype's
oriented natural balance, with `U=Y*q²`, `a=X*Y+Y`, `H=3+4*a`:

```
U*main + H*k = U*(X+a*c) + H*(U*gamma+R+1).
```

In particular, the prototype carrier has no additional `X*Y*q` term. Since
`U=q⁵*s`, rearranging and reducing mod `q⁵` yields
`H*(R+1) ≡ H*k (mod q⁵)`, and hence
`q⁵ ∣ H*magnitude(R+1,k)`. The existing IΣ₁ source theorem
`ArithmeticAdaptiveFactorThree2011.cancel_factor_three` has exactly the
needed inputs `q>0`, `q³∣Y`, and `H=3+4Y(X+1)`; it concludes
`q⁴∣magnitude(R+1,k)`. Its source handles both `3∣q` and `3∤q` internally.
No coprimality or Bézout certificate is assumed by this client. This is a
source-level application, not a checked compilation or a new proof of that
imported theorem.

`rank_congruence_of_main_norm` additionally proposes deriving the oriented
balance using `DirectMainNorm.direct_main_orientation`, with explicit
`Y≥8`, `k>0`, `q>0`, and the prototype's exact natural signed-pair norm. The
lemma accepts arbitrary natural eta, **including eta=0**; the graph must
still supply that norm and its signed-pair representation.
`early_index_of_actual_carrier` composes the congruence with the separately
unelaborated `ResidueFirstIndexModelDraft.early_index_of_natural_norm`. It
explicitly requires positive X, the natural first norm and the rank window;
it returns its actual index n, quotient w, Pell coordinates and q⁴ residue.
The bounds and port facts must be established on the prototype graph, and
`R≥26` for the later contradiction remains separate from this source's
`R≥24` premise.

The unit-product zero-to-factors proof, signed/natural norm extraction,
positivity, representation of the exact graph rank and fixed ports, auxiliary
witness, eta-zero contradiction, graph-zero maps, compatible providers,
`#print axioms` results and any internal iPRA proof all remain open. This
packet does not update a displayed equation or claim a smaller proved graph.

Run `python3 -I -S -B research/ordinary13-eta-zero-early-congruence-model-draft/check.py`
from `Computability/DiophantineConsistency`; compare its output with
`receipt.json`. The checker verifies source interfaces and finite algebraic
controls and does not execute Lean.
