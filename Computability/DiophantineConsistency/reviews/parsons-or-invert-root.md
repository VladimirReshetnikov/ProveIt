# Height-preserving disjunction inversion

`ParsonsOrInvert.invert` replaces any selected occurrences of `A ∨ B` in a
cut-free one-sided sequent by both `A` and `B`, preserving cut-freeness and
not increasing proof height. Its selection and contraction cases handle
arbitrary duplicates. `invert_below_exs` specializes this to a side formula
at any context position and yields a derivation strictly below the original
existential conclusion, without a permutation or contraction step.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. Both
axiom reports list only `propext` and `Quot.sound`. The [16-file replay
manifest](parsons-or-invert-replay/FILES.json) has SHA-256
`a4c0d3ef52034da19a4fb428b5d4ec6c999f3d72d60fb7639130c964b0036e1f`.
This module imports Foundation's cut-free calculus directly; Foundation and
package objects are an inherited boundary, not a fresh transitive source audit.

This is a source-derivation transformation, not a general Π₂ normalizer,
global recursion, conservation theorem, or PRA-provability result. The HA
theorem for the maintained 14-variable PDF equation is complete separately.

A third independent replay at `/tmp/parsons-or-invert-build-3po8uzgk` passed
with matching source, object and complete log hashes under the same inherited
Foundation and package boundary.
