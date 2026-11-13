# Fresh-base plan for the 67-operation, degree-106 endpoint

This is a **source plan**, not a new Lean check or replay. The explicit
[67-operation graph](../fourteen-normalized-product106/polynomial.json) has
14 positive inputs, integer leaves, 38 multiplications, 16 additions and
13 subtractions. Its exact degree 106 at the current positive beta is a
separate [finite certificate](../fourteen-normalized-product106/CERTIFICATE.json),
not a Lean `totalDegree` theorem. The existing
[`ModelCarrierCurrent`](../../Lean/DiophantineConsistency/ModelCarrierCurrent.lean)
source already states the same-zero and native, standard and equality-only
iPRA endpoint theorems. Its author and peer stage-79 checks use the current
source bytes, but their direct model providers differ in hash and the checks
inherit earlier package and transitive ancestry; see the
[paired-stage record](../../reviews/nine-variable-ipra-peer-stages-76-80/README.md).
They are not a fresh coherent extension of the current14 base.

## Smallest source-declared route identified so far

The successful current14 project rebuild already contains
`HACurrentEquation2011`, `HACurrentAssembly2011`, `ArithmeticCurrentSentence2011`,
`CurrentEquationSyntax2011`, and the native/standard iPRA transfer chain.
The read-only [source preflight](../normalized106-current14-sixteen-source-preflight/README.md)
identifies 16 additional repository modules (and 991 shared modules) for
the roots `ModelCarrierScaled`, `ModelCarrierSyntax`, `ModelArithmetic`,
`IPRAExpressionNative`, and `HACurrentEquation2011`, if the small
same-zero-to-bridge argument is written locally instead of importing
`HAExpressionSameZero` (whose import brings the unrelated 86-operation lane).
The resulting provider order, among these 16 modules only, is:

```
AdaptiveEquationSyntax2011, ConsecutivePell, DiscreteOrderedRingFacts,
HAExpressionAssembly, ShortEquation, TotalDegreeBound, WeightedExpressionDegree
ModelDifferenceRing         <- AdaptiveEquationSyntax2011, WeightedExpressionDegree
PRAExpressionZFCStrict      <- HAExpressionAssembly
ShortCircuit                <- ShortEquation
IPRAExpressionNative        <- PRAExpressionZFCStrict
ModelArithmetic             <- ModelDifferenceRing, DiscreteOrderedRingFacts
ShortSystem                 <- ShortCircuit, ConsecutivePell, TotalDegreeBound
Carrier65                   <- ShortSystem
ModelCarrierScaled          <- DiscreteOrderedRingFacts, Carrier65
ModelCarrierSyntax          <- WeightedExpressionDegree, ModelCarrierScaled
```

This is only a **project source-import count**, not a compiled-header or
dynamic-load compatibility proof. In particular,
`Mathlib.Algebra.MvPolynomial.CommRing` is one of five newly declared external
imports, and its transitive compiled-header survey was not exhausted. The
previous printed-port experiment demonstrated that Foundation and a Mathlib
Matrix provider can collide. A fresh coherent extension must check the actual
provider closure and observe each Lean result; neither the count nor the old
paired stage establishes compatibility. No claim is made that 16 is minimal.

## Local client and exact hypotheses

Use the existing `ModelCarrierSyntax.expressionAt106` as the 67/106 syntax and
bind its ring evaluation with `evalRing_expressionAt106`. Recreate the small
`sameZero106` argument from `ModelCarrierCurrent` on the fresh provider:

1. In each model `V` of `𝗜𝚺₁`, use its difference ring `DiffRing V`,
   `ModelArithmetic.model_discrete`, `ModelArithmetic.mod4`, and the positive
   cast of the current beta. A positive shift supplies all fourteen positive
   coordinates. `ModelCarrierScaled.delta_pos` gives `delta>0`.
2. Apply `ModelCarrierScaled.zero_iff106` at those ports and coordinates,
   and `internalZero_iff`/`internalZero_positiveShift` to identify the literal
   zero with `ObjectCurrentEquation2011.naturalExpression`. This is
   same-valuation equivalence in **every stated model**, not just in ℤ.
3. Inline the generic proof in `HAExpressionSameZero.bridge`: for each such
   model, use `HAExpressionAssembly.classicalNoZero_iff` twice and
   `forall_congr'`/`not_congr` on `sameZero106`, then compose with
   `HACurrentEquation2011.polynomialBridge V`. The resulting local value has
   type `HAExpressionAssembly.PolynomialBridge (positiveShift expression106)`.
   `FoundationHACurrentNoZero2011.classicalSentence` is defined as
   `classicalNoZero ObjectCurrentEquation2011.naturalExpression`, so this
   composition targets the existing current equation's exact sentence.
4. Apply `IPRAExpressionNative.equivalence_of_bridge`; transfer the result
   with `IPRAStandardTheory.provable_iff` and, if needed, the existing
   equality-only erasure. The theorem must retain the selected mapped
   refutation predicate and be accompanied by expected axiom reports. This
   would prove existence of the internal derivation, not either side alone.

The zero equivalence is not merely cancellation by positive `delta`: the
67 graph also changes the auxiliary coefficient. Its product-zero condition
makes `strong` a unit, and the generic mod-4 exclusion of `-1` makes it `1`;
only then does `delta*(f²-1)=delta²*(i*c²)²`. The existing model proof includes
that step through `ModelCarrierScaled.replace_coefficient`; it must not be
replaced by an integer-only `CarrierNormalizedProduct106` theorem. Its
`delta_pos` proof needs positivity of the fixed beta and shifted coordinates;
it does not assume a zero.

## Alternative and required checks

A second source route starts with the all-model same-zero result, uses
completeness for an `𝗜𝚺₁` iff between the two classical no-zero sentences,
applies `PRANoZeroUnary.noZero_unary_open` twice and
`PRAISigmaOneOriginalEquivalence.comparison`, then translates the PRA iff
via `IntuitionisticPRABridge.from_classical`, `IPRAIffGG.unpack_iff_image`
and `IPRAMappedNoZero.mapped_gg_noZero`. Those transfer modules appear in
the current14 source manifest. It could reuse the fresh native endpoint
instead of the machine bridge, but requires a new generic composition and
exact syntactic alignment; no new Lean check or smaller closure is known.
The existing `HACurrentEquation2011.polynomialBridge` route above is the
more direct use of the present source.

Before reporting the new endpoint, independently bind the 67-row JSON graph
to the Lean syntax, build the new sources against one coherent fresh base and
its compatible dependencies, check the actual terminal exits and axiom
reports, and distinguish that evidence from the historical stage-79 build.
The retained external coefficient/JSON/PDF correspondence, package-transitive
and dynamic ancestry, and any human-readable display binding remain separate.
