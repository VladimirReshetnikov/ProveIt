# Difference-ring evaluation to signed-pair representation — source draft

This graph-independent draft connects two existing arbitrary-model interfaces.
Given an **explicit hypothesis** that an expression's difference-ring
evaluation is `ι a−ι b`, `represented_of_ring_eval` proposes that its
`pairEval` is cross-sum equivalent to `(a,b)`. The proof uses
`ModelDifferenceRing.split_evalRing`, `evalSemiring_map`, and injectivity of
`ι`; it does not assume an interpretation in the standard integers.

`product5_first_iff` transports a five-factor signed-pair equivalence through
replacement of the first factor by an equivalent pair. The final theorem
composes this transfer with the independently source-reviewed
[five-unit fact](../ordinary14-five-unit-model-facts-draft/) for a stated
first-factor evaluation, `m≥2`, a stated product equivalence to one, and three
explicit modulo-four negative-unit exclusions. The fourth factor is an
unrestricted guard.

This does not prove the 75/74 literal first evaluation or product shape,
obtain a product equivalence from `InternalZero`, establish `m≥2` from the
ports/coordinates, establish the three residue hypotheses, derive any guard
premise, or bind a model/halting/iPRA endpoint. Natural-port and positivity
assumptions must be stated by future clients. The imported `FiveUnitFacts` is
itself an unelaborated draft. Source signatures and tactics remain unchecked by
Lean; provider transitive coherence and physical-byte/PDF binding remain open.
No Lean run was performed.

Reproduce the finite signed-pair controls and source hashes with:

```
python3 -I -S -B research/ordinary14-pair-eval-ring-bridge-draft/check_source.py | cmp - research/ordinary14-pair-eval-ring-bridge-draft/observation.json
```

These controls do not establish Lean elaboration or any graph evaluation.

Independent source review: [pair evaluation ring bridge](../../reviews/ordinary14-pair-eval-ring-bridge-independent/README.md).
