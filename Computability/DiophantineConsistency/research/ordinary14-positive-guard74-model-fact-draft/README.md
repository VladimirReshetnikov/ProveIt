# Positive 74 shifted-guard strictness — source draft

This is a fact-level ordered-ring draft for the separately reviewed
[all-positive 74-operation shifted-guard graph](../ordinary14-positive-guard74/).
It assumes a discrete linearly ordered commutative ring, positive F, alpha and
X, nonnegative K, `q≤X`, `1≤h`, and the exact guard equation
`(q−F−alpha)*(X+K)−F=b*(h−1)`. It concludes `1<h`. No sign assumption on b is
needed for this conditional inequality.

The proof assumes h=1, so the guard equality makes `(q−F−alpha)*(X+K)=F>0`.
Since X+K>0, the first factor is positive and, by discreteness, at least one.
Positive alpha then gives F<q≤X, so the left product is at least X+K>F, a
contradiction. This is not a graph theorem: the literal guard identity,
`q≤X`, positive hypotheses, and equality from the candidate's own zero
remain separate model-client obligations. The unrelated mixed-F-shift 74
candidate has a different coordinate domain.

The theorem and tactics are unelaborated. It does not establish provider
compatibility, a 74↔75 model equivalence, halting/iPRA endpoint or physical
byte/PDF binding; no Lean run was performed.

Run the finite controls and source-hash receipt from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-positive-guard74-model-fact-draft/check_source.py | cmp - research/ordinary14-positive-guard74-model-fact-draft/observation.json
```

The control with `q=5, F=3, alpha=1, X=1, K=2, h=1` shows that the
`q≤X` premise cannot be dropped from this fact. It is not a full graph zero.

Independent source review: [74 shifted-guard strictness](../../reviews/ordinary14-positive-guard74-model-fact-independent/README.md).
