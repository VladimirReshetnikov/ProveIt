# Ordinary principal logical cases

`ParsonsLogicalCases` gives actual PA-minus rule-calculus proof transformers
for the principal existential, universal, disjunction, and conjunction side
rules. The universal case explicitly shifts the free parameters of its side
formula under the eigenvariable. The corresponding `_case` theorems apply
these transformers to cut-free premise derivations and invoke only explicit
local recursive hypotheses at heights strictly below the enclosing LK
inference. For conjunction both premise derivations are required. No height
comparison crosses the earlier cut-elimination pass.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Eight
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-logical-cases-replay/FILES.json) has
SHA-256 `04a95dd43814e44d73e7a6a3d4343fc8c3838c7996c9f96066b1323ebcc6421a`.
The `ParsonsGuardedCollection` provider has source SHA
`f96d84833ba37cb112e46dffdaf2a835f7af7be806d1bb1a9010911a7c299d03` and
object SHA `4ad9c64484f1518e43be1e75366cfd6e3ac9fb03af72d4df4b0605dc280c9287`;
`ParsonsPrenexAll` has source SHA
`8dd536e5a0c384c280fcf8405dbb70aeda14eabc45104e4e94f371e12508bc94` and
object SHA `7e81664dd299eaa6cefd509c47863a86ba81023b55034a10932fc14a838b93e5`.
Both current source files match their frozen provider snapshots. The earlier
provider chain is described in their receipts. Foundation/Mathlib and
completeness objects remain an inherited boundary, not a fresh transitive
audit.

These are principal side cases, not a proof of the complete recursion. In
particular they do not handle arbitrary nonprincipal context occurrences,
contraction, classification/normalization of every side context, or special
induction-axiom blocks. The local recursive hypotheses remain to be supplied
by a single global induction; no conservation or PRA witnessing theorem is
claimed.

## Independent root replay

A third build at `/tmp/parsons-logical-cases-build-m6nw7e8p` passed; its
sources, objects and complete logs match both author runs. Its direct guarded
collection provider matches the independently replayed object. The [independent
artifacts](parsons-logical-cases-replay/root-build/) are preserved; the
Foundation/Mathlib boundary remains inherited.
