# From a strict-induction proof to the rule calculus

`ParsonsStrictInitial.strict_fragment` takes an **actual Foundation proof** of
an arithmetic sentence from PA-minus together with the induction scheme for
`Strict` predicates: finite existential prefixes over Σ₀ matrices. Given a
Tree descriptor for the embedded conclusion, it produces a Lean existence
proof of an actual `ParsonsRule.Proof 𝗣𝗔⁻` of that conclusion.

The proof normalizes the given theory proof to an actual cut-free derivation,
certifies the initial marked context (Tree conclusion, strict induction
blocks, and actual PA-minus base shapes), applies the closed global marked
recursion, and extracts the original conclusion. It assumes no height
comparison across cut elimination.

Both restrictions are material: the theorem does **not** convert arbitrary
Foundation Σ₁ induction to strict induction, nor does it derive Tree
descriptors for all Π₂ conclusions. The resulting calculus still includes a
Σ₁ induction rule and is not identified here with candidate PRA. This
conservation route is separate from the already completed HA result for the
14-variable PDF equation.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The four
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx` is reported. The [16-file replay manifest](parsons-strict-initial-replay/FILES.json)
has SHA-256 `1532bc774ced798b6ed73b7ddf5c2b14f2eab57e70b60a9dce888019eb846294`.
The direct GlobalStrict source hash
`15012a6e100236ca2898327bcdad56ac95a29888fe5bb814b3dc82473a867739` and
object hash `b02cb8f7294a4b77c0b7b0945d26f655a09c8a93f2043dabc5e18f879c7a0f51`
match its frozen provider. Earlier providers, Foundation/Mathlib, and
completeness objects remain an inherited boundary, not a fresh transitive
audit.

A third independent replay at `/tmp/parsons-strict-initial-build-dfju_h2r`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
