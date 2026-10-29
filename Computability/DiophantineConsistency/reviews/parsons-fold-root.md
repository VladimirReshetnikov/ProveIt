# Base-only branch for an arbitrary side context

`ParsonsFold.fold_context` turns any finite initial portion of an LK sequent
into one disjunction while retaining the remaining context. `logical_leaf`
therefore turns an arbitrary all-logical sequent derivation into a rule proof
of its full side disjunction. `base_leaf` gives the stronger base-only branch:
from an arbitrary LK derivation of a finite side sequent together with the
negations of finitely many actual PA-minus axioms, it constructs a rule proof
of the side disjunction. It uses the finite-context embedding to discharge
every axiom; their PA-minus membership certificates are explicit. There is no
local recursive hypothesis and no cut-free restriction for this branch.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Three
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`; the
sequent-folding derivation does not use choice. The
[16-file replay manifest](parsons-fold-replay/FILES.json) has SHA-256
`55080d127056f220b8ddaeeb2c4d27b3c4590957aa0009cbe834c303d7d53a31`.
The direct `ParsonsStructure` provider has source SHA
`d9e2735b67c4b01fb1aea0d223bcf194c800d8fa29673078634ef0d095876c83` and object
SHA `e6a4bf7137288fda68f43d21f6a0155aae37b62acd17dd92f665e988f070ea80`;
`ParsonsRuleEmbedding` has source SHA
`076a1d32a29e9bf4e257bb3f2d6e9965677e786dfca0c12720cc58afc26847a1` and object
SHA `b85ce569b406c04a2fd74e85a036b49a657b9fbaaa9808e87fadabd7aa8565df`.
Foundation/Mathlib and completeness objects remain an inherited boundary, not
a fresh transitive source audit.

This closes the branch with no special induction block. It does not remove
such blocks, define the complete global side-classification invariant, or
prove the overall cut-free translation or PRA witnessing.

## Independent root replay

A third build at `/tmp/parsons-fold-build-jorff0zk` passed; its source, object
and complete-log hashes match both author builds. The structural provider
matches the independently rebuilt object. The [independent artifacts](parsons-fold-replay/root-build/)
are preserved; the Foundation/Mathlib boundary remains inherited.
