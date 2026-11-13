# Proposed all-model bridge for current2011 adaptive 88/30

This packet is **source only**. It proposes a same-valuation zero
equivalence between the exact current2011 88/30 four-square expression and
the existing 87/51 adaptive literal in every `IΣ₁` model, followed by a
native-iPRA derivability transfer **conditional on the exact 87 parent
`PolynomialBridge`**. None of the generated syntax, generic factor proof,
model client, local imports, tactics, provider selections or resulting
theorems has been elaborated. No new iPRA endpoint or formal JSON/PDF
semantics is claimed.

## Three proposed components

1. [`AdaptiveFourSquare88Graph.lean.src`](AdaptiveFourSquare88Graph.lean.src)
   is deterministically generated from the pinned
   [88-row graph](../adaptive87-four-square-current88-30/graph.json). Its
   fields expose all four residuals and the factor variables. Its `parent`
   field uses the actual 87 parent association `Fs*(Fa*(F0*F1))−1`;
   `parent_eq` proposes definitional equality with
   `AdaptiveFirstRootFactor87Literal.expressionAt87`.
2. [`FourUnitGeneric.lean.src`](FourUnitGeneric.lean.src) proposes the
   generic discrete ordered-ring equivalence between a four-factor unit
   product and four squared deviations. Its factor exclusions map through
   a ring homomorphism to the **existing public universal**
   `ArithmeticAdaptiveFactorUnits2011.first_bad`, `main_bad`, `aux_bad`,
   and `strong_bad` ZMod-4 lemmas. They require no positive witnesses or
   port bounds. Product-one units are split using the repository's
   `DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one`.
3. [`FourSquare88Model.lean.src`](FourSquare88Model.lean.src) proposes
   evaluating all four exact graph factors in `DiffRing V`, binding them to
   those mod-4 shapes, using `ModelArithmetic.mod4` and `model_discrete`,
   and applying the generic result in both directions. Its `sameZero`
   applies positive shift at the same valuation and current tuple. Its
   `bridge` and `native_equivalence` keep the exact 87 parent bridge as an
   explicit hypothesis. The repository source
   `HAAdaptiveFactor87.polynomialBridge` states that parent interface, but
   this packet does not instantiate or replay it.

The separate [external 88/30 packet](../adaptive87-four-square-current88-30/README.md)
and its [independent review](../../reviews/adaptive87-four-square-current88-30-independent/README.md)
prove/check the standard-integer zero argument, graph and fixed-port degree
with their stated limits. Those results do not automatically check this new
model source. The historically paired 87 translated-refutation endpoint,
its exact target distinction, and all inherited source/object/package
ancestry remain as described in the external packet.

## Static checks and open work

[`check.py`](check.py) pins the direct source files and the external graph
receipt, reproduces the generator, compares all 88 emitted let rows to the
JSON and all 87 parent rows to the actual Lean source, and checks the exact
factor and bridge interface markers. This is a deterministic text/row check,
not Lean parsing, elaboration, a theorem about external JSON or physical
bytes, or an authenticated provider plan.

The proposed `rfl` parent binding; `ZMod 4` map simplifications and
`linear_combination`; ordered-ring factor and nonnegative-square tactics;
large expression evaluation/`ring`; implicit arguments, heartbeats and local
import resolution; exact current port expression; and every `#print axioms`
or iPRA result remain untested. A coherent source selection, compatible
providers, bounded Lean build, artifact audit and independent replay are
needed before claiming the model equivalence or internal endpoint. No
consistency, absence of solutions, or global minimality is asserted.

```
python3 -I -S -B research/adaptive87-four-square-current88-model-draft/check.py > /tmp/adaptive88-model-source.json
cmp /tmp/adaptive88-model-source.json research/adaptive87-four-square-current88-model-draft/result.json
```

No Lean/build or staging operation is performed.
