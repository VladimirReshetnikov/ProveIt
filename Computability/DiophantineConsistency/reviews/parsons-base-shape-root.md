# PA-minus axiom shapes and base-state transitions

`ParsonsBaseShape.PrefixSigma` means zero or more leading universal
quantifiers followed by a formula in Foundation's Σ₁ hierarchy. Lean proves
this shape for **every actual PA-minus axiom**, including the arbitrary-arity
function and relation congruence cases of its equality theory. It follows
that each axiom has the Π₂ certificate needed to initialize `BaseState`.
`prefix_rew` preserves the shape under arbitrary term rewrites.

`ShapedBase.initial` constructs the enriched base state directly from an
actual PA-minus membership proof. `openState` preserves the shape when a
negative universal is opened at a witness; `shiftState` preserves it under
an eigenvariable shift. `nonterminal_is_all` proves that a shaped state which
is not already Σ₁ has an exposed leading universal. Thus, when this state is
integrated into the marked context, it can either take the strictly
height-decreasing negative-universal case or reclassify its terminal Σ₁
positive theorem as a Π₂ side and discharge it.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Nine
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-base-shape-replay/FILES.json) has SHA-256
`53ca247987772c84eca60973cac718dd3ecb8f8a97baa0241c958dbc77d30e72`.
The direct `ParsonsBaseState` source hash
`f5df92a77427263307dd5196e57c78fdd0744aa0c84e28a6d0b7c8357a38f1e6`
matches its frozen snapshot; the provider object hash is
`fae668fa4e5f3934c0af4157592ee827b66b9a51b71bd966dc51206aa45ec4d2`.
The earlier provider chain, Foundation/Mathlib, and completeness objects are
an inherited boundary, not a fresh transitive audit. Exploratory scratch
failures around embedding and quantifier inversion were corrected; their
console logs were not retained.

This closes the PA-minus shape obligation, not the global recursion. The
shaped state is not yet integrated into `ParsonsInvariant.Entry`; terminal
reclassification uses the same derivation height and therefore needs a
secondary well-founded measure. The general Π₂-to-Σ₁ guard adapter, the
single global induction, and PRA witnessing remain open.

## Independent root replay

A third build at `/tmp/parsons-base-shape-build-xq21ujtd` passed; source,
object and complete-log hashes match both author runs. The base-state provider
matches the independently rebuilt object. The [independent artifacts](parsons-base-shape-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary. The source
disables the `flexible` linter locally for `sigma_body_of_all`; proof checking
remains enabled.
