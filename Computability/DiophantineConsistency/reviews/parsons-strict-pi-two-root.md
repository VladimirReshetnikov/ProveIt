# Strict Π₂ sentence endpoint

`ParsonsStrictPiTwo.strict_fragment` specializes the normalized strict
fragment to any closed sentence `∀x₁ … ∀xₙ ∃y D(x₁, …, xₙ, y)` whose matrix
`D` is Σ₀. From an actual Foundation proof using PA-minus plus the induction
scheme for strict existential-prefix Σ₁ predicates, it constructs an actual
`ParsonsRule.Proof 𝗣𝗔⁻` of the embedded sentence. The required Tree
descriptor is built automatically from the bounded matrix.

This matches the formula shape of the separately proved candidate-PRA
bounded-witness endpoint, but **does not connect the two endpoints**: a
translation or restricted comparison from this intermediate rule proof to a
candidate-PRA theorem is still required. The theorem also does not convert
arbitrary Foundation Σ₁ induction to strict induction. The completed HA result
for the 14-variable PDF equation is separate from this conservation route.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
three axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`;
no `sorryAx` is reported. The [16-file replay manifest](parsons-strict-pi-two-replay/FILES.json)
has SHA-256 `1cfeeaf95f6ce4be88fabc1526268f95a9456ab0cda46e2b8d539d0633b4ff69`.
The direct StrictInitial source hash
`86667100598f5d98d4ec1e1635b556fc7296cb573b5ad82958e31dc1484d9eb0` and
object hash `86b53d4a1839dbc8c0df26c38f9b65749dc9d221fa55fcb81ac01a70fe2549ab`
match its frozen provider. Earlier providers, Foundation/Mathlib, and
completeness objects remain an inherited boundary, not a fresh transitive
audit.

A third independent replay at `/tmp/parsons-strict-pi-two-build-5amamm0t`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
