# Direct-first five-unit model fact — source draft

This source-only draft packages the factor-level core of the independently
reviewed [75-operation negative-Pell finalizer](../ordinary14-negative-pell75/)
using the natural signed-pair representation of an arbitrary IΣ₁ model. It
never imports `ModelArithmetic`. The first factor is the explicit pair
`(x*x, (m*k)*(m*k+k))`, with the indispensable premise `2≤m`. Its negative
unit is excluded by the existing internal bounded-descent theorem
`ArithmeticNegativeNorms.consecutive_ne_negative`; the polynomial identity
reduces the required equation to that theorem's exact shape.

`five_positive_of_direct_first` uses existing
`ArithmeticSignedPairs.product5_positive` and the existing residue-to-sign
lemma `ArithmeticAdaptiveFactorUnits2011.negative_residue`. The three other
restricted pairs are required explicitly to avoid residue `−1`; the fourth
pair is an unrestricted guard. Given the **actual signed-pair product**
equivalent to one, the conclusion gives all five factors equal to +1.
No sign condition is imposed on the guard. The finite ZMod-4 theorems
`main_bad`, `aux_bad`, and `strong_bad` in the imported factor module are
plausible ingredients for discharging those three residue hypotheses, but
this draft does not bind them to the 75 graph.

The reviewed all-positive [74 shifted-guard graph](../ordinary14-positive-guard74/)
adds a separate reverse-map obligation: derive from its own zero and explicit
`beta>0`, `K0≥0`, positivity and `X≥q` that the shifted guard coordinate is
strictly greater than one. The separate [mixed-domain graph](../ordinary14-mixed-guard74/)
uses a different F shift and is not an all-positive replacement.

This draft does not establish the graph's signed-pair representation,
`m≥2` from model ports/positive inputs, the three modulo-four pair
hypotheses, any 74↔75 graph map, `InternalZero` binding, model-halting bridge,
or iPRA endpoint. `ArithmeticNegativeNorms`, `ArithmeticSignedPairs`, and
`ArithmeticAdaptiveFactorUnits2011` objects were observed under the retained
P72/base route; this does not establish coherent transitive providers or
compatibility of a new build. Source signatures and tactic scripts are
unelaborated. No Lean run, provider replay, byte/PDF binding or endpoint proof
is claimed.

Reproduce the finite controls and source-hash receipt with:

```
python3 -I -S -B research/ordinary14-five-unit-model-facts-draft/check_source.py | cmp - research/ordinary14-five-unit-model-facts-draft/observation.json
```

These controls do not prove the unbounded statement or check Lean elaboration.

Independent source review: [five-unit model facts](../../reviews/ordinary14-five-unit-model-facts-independent/README.md).
