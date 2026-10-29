# Contraction and base-axiom elimination

`ParsonsStructure.disjoin` represents a finite side sequent as a disjunction.
`projected_weakening` transports an actual PA-minus rule proof across any
subset of sequents under any fixed formula projection. `contraction_case`
uses this transformer for an actual cut-free contraction inference; its
explicit recursive hypothesis is applied to the premise at strictly smaller
height. This accounts for arbitrary order, repeated formulas, and omitted
formulas under that fixed projection.

`remove_base` discharges a negative occurrence of an actual PA-minus axiom
from a rule proof of its disjunction with E. The axiom membership is an
explicit hypothesis; the transformer uses the existing rule-calculus axiom
constructor and logical resolution.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Five
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-structure-replay/FILES.json) has SHA-256
`76d20fff3644933a1cb3d83139471048b06805c98c621e9aa03d1c09fb21d523`.
The direct `ParsonsGuardedCollection` provider and inherited provider chain are
described in [its receipt](parsons-guarded-collection-root.md); Foundation,
Mathlib, and completeness objects are an inherited boundary rather than a
fresh transitive audit.

The result does not define the required global formula projection or show it
is stable under all LK rules and special induction blocks. Its recursive
hypothesis is local and explicit; no full cut-free translation, conservation,
or PRA witnessing theorem is claimed.

## Independent root replay

A third build at `/tmp/parsons-structure-build-u_t7iwz4` passed; its
sources, objects and complete logs match both author builds. The guarded
collection provider matches the independently rebuilt object. The [independent
artifacts](parsons-structure-replay/root-build/) are preserved; the
Foundation/Mathlib boundary remains inherited.
