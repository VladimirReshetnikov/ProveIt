# Conditional q-divisibility for the actual positive 84 graph

This is an unelaborated model-source draft. It does not establish the
84-side `q | X` cut, Lean/provider validity, or any iPRA endpoint. It reduces
that cut to two explicitly stated graph facts and records the circularity to
avoid in trying to supply them.

For a positive 84 valuation, the actual graph has `q=1+J*beta`, `X=v 6`,
`Y=q³*s`, `U=Y*q²`, and main shift `U*gamma+X*Y*q-(k-R-1)`.
`OrientedIndexCut` asks for a same-model index quotient and a natural main
root satisfying the exact decomposition and **extra-term** oriented balance:

```
k = R+1+4*X*Y²*w
U*main+H*k = U*(X+a*c)+H*(U*gamma+X*Y*q+R+1).
```

The existing source-only `ResidueThreeProjectionDraft.q_dvd_threeX` proposes
`q | 3*X` from exactly those facts and the literal `Y=q³*s`; it does not
assume `q | X`. The separate `PowerGraphCut` asks for an exponent with
`X=Exp.exp R`. Given both graph cuts, the proposed client applies
`ModifiedCarrierFactsDraft.compact_beta_divides_X`, which uses the symbolic
compact port beta `2^(67*8807)-1` and the existing Mersenne cancellation to
obtain `q | X`. The two cut exponents need not agree for this last deduction.
The graph must still supply both facts; in particular the source `q | 3*X`
projection is not itself a proof of either graph cut.

## What the available unscaling and power chains do and do not supply

* The scaled-first quotient lemma is useful on the **87** graph: a positive
  87 zero plus its signed first norm yields `q³ | Y`. On the 84 graph,
  `Y=q³*s` is already a definition. That quotient does not give `q | X`.
* A separate source proposal maps an 84 zero to an 87 zero by switching the
  first root. Its `ReverseInputs` still require the actual 84 large-k bound
  and represented positive beta. Even with that step, a witness-preserving
  87→original literal map, compact port bounds and applicable original
  `graph_power`/`graph_projection` sources must be established. The latter
  are about a different, 12-input literal; they cannot be directly applied
  to the 84 or 87 JSON graph.
* The existing eta-natural `power` theorem assumes `X=q*w0` and uses the
  no-extra-`X*Y*q` carrier. Supplying that premise from an arbitrary 84 zero
  already requires the missing `q | X` positive quotient, so using that
  theorem via 84→83 to prove `q | X` would be circular. A direct modified-
  carrier power theorem or a separately proved 84→87→original path would
  avoid this particular circle, but neither is supplied by this packet.

The simple non-Mersenne scalar values `q=3`, `X=8` satisfy `q | 3X` and
`X=2³` but not `q | X`; they are not claimed to be a graph zero. Thus the
specific compact Mersenne port identity is material to the cancellation.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive84-division-model-draft/check.py
```

The read-only receipt pins the direct sources and graph rows and checks
bounded integer instances of the oriented projection. It does not verify
Lean syntax or tactics, all-model graph facts, provider ancestry, axioms, or
the physical PDF.
