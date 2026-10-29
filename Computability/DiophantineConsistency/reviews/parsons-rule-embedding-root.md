# Finite theory proofs in the Σ₁-rule calculus

`ParsonsRuleEmbedding.fromContext` takes an actual Foundation LK derivation
of `χ :: ∼Γ` and a rule-calculus proof of each formula in the finite context
Γ, then constructs a proof of χ. The recursive proof discharges one context
formula at a time by LK disjunction introduction and modus ponens; it handles
free formulas, repeated entries, and derivations with cuts. `embedTheory`
uses this to convert any Foundation `Theory.Proof T σ` into a rule-calculus
proof of the embedded sentence **over the same T**. `embedCutFree` accepts
the cut-free package directly, and `provable_embeds` is the corresponding
existence theorem.

No axiom has been eliminated: applying this to IΣ₁ retains IΣ₁ as the base
theory. Its role is to discharge proofs over the base theory and supply a
finite-context interface to the later cut-free reduction; it is not an
IΣ₁-to-PRA or IΣ₁-to-rule conservation theorem.

The final main and checks were snapshotted and built twice in fresh private
outputs with Lean 4.32 `-M6000 -j1 -DElab.async=false`. Both objects and
complete logs match; no warnings were emitted. Four axiom reports use only
`propext`, `Classical.choice`, and `Quot.sound`. The [24-file replay manifest](parsons-rule-embedding-replay/FILES.json)
has SHA-256 `65c9889e559d741c88e502f0b8dc43431e6b060b80217008b28b923a64d143e5`.
The initial main compiled but the check failed because Lean cannot eliminate
an `Or` proof into a `Type`-valued proof object directly and because an
example omitted `noncomputable`; the second and third builds passed after
using `Nonempty` with classical choice and marking the check section.
That failed build's snapshots and logs remain in the bundle.

The direct imports use previously built `ParsonsRule`, `ParsonsGuard`, and
`ParsonsCutFree` objects. Their SHA-256 hashes are respectively
`eb5c49e2362e7d7f05b6e7dea5d0f671134657c57f0f09a9ec959f7c01a57ec3`,
`6ed2a4c0e10113e0c82c64ca7a4e05c0ff965a51f1ed3e3ad16400d3d7a728d1`, and
`93461a90f9f33d21e8a07a87fe0971f31108e51454800b746c4684ed2bb1f436`.
The Foundation and Mathlib compiled-object trees are an inherited boundary,
not a fresh transitive source audit.
