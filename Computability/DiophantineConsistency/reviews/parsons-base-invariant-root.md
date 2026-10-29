# Marked base-state invariant

`ParsonsBaseInvariant.BaseGood` records the exact positive-prefix certificate
for every marked base state. `initial_base` proves it for every initial
normalized context from actual PA-minus axiom membership. The certificate is
preserved by eigenvariable shifts, duplicate-safe contraction selection, and
opening a negative universal at any witness. `terminal_good` proves that
reclassifying a terminal positive base theorem as a negative side preserves
all three conditions: Tree side descriptors, strict induction blocks, and
base certificates. That transition is still at the same derivation height and
requires the separate base-count measure.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
five axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-base-invariant-replay/FILES.json) has
SHA-256 `1155318923e52e498f0a82226e805fb4c45c9a85b1660a3e2002aeb8b7a1f636`.
The direct BasePositive source hash
`125471eb5ab19723c3b6c78bf823278a5cf35b81f267c1c0619121b291df4026` and
object hash `b4c90e2831c0fc979d0e04e6a013eace2619dfae0578a1d026270d8059a8cacd`
match its frozen provider. Earlier providers and Foundation/Mathlib remain
an inherited boundary, not a fresh transitive source audit.

This tracks the base conditions; the global well-founded recursion and the
reduction of arbitrary Σ₁ induction to strict induction remain open.

A third independent replay at `/tmp/parsons-base-invariant-build-qjlb5ptd`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
