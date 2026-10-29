# Guard descriptors for finite strict existential prefixes

`ParsonsStrictPrefixTree.strict_step` constructs a Tree descriptor for the
original step formula of every induction predicate `∃y₁ … ∃yₙ D(x, y₁, …, yₙ)`
with Σ₀ matrix `D`, arbitrary finite `n`, and arbitrary free parameters.
`strict_negative` constructs the descriptor for the negative counterexample
side at any witness term. Their proofs use `ParsonsGuardClosure.closure` to
describe the universal prefix arising from negating the existential prefix;
no source normalization is performed. The zero-prefix bounded case is included.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-strict-prefix-tree-replay/FILES.json) has
SHA-256 `a1306125d3728312cda0955e0fd12d542d2c9fb50ba15eee2f850b32f51ec247`.
Direct sources and provider objects are:

- `ParsonsGuardTree`: source `409662779f56e90637900537dfbc78276f87362eb30f9a520c6aaf2f33e5b9c0`, object `9deaab2f8a25685a1c4fa7b564a68335529bcf93bc704f1d7ae4c55916621d7c`.
- `ParsonsGuardClosure`: source `91c14fd441ce5421f7e2adc7e7d4ba5b3f490992b24f2998b0005df61d41a20f`, object `ff15e6e9e39dca2dd1898a1518482742ef56c4a0f5c9a3d3a26452f689c3b19a`.

The GuardTree source matches its frozen snapshot; GuardClosure uses the
independently replayed provider recorded in its own receipt. Earlier providers
and Foundation/Mathlib are inherited, not a fresh transitive source audit.
The restriction to strict existential prefixes is material: arbitrary
Foundation Σ₁ predicates, global induction, conservation, and the desired
PRA-provability result remain open. The separate HA theorem for the maintained
14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-strict-prefix-tree-build-l2phr1hs`
passed with matching source, object and full-log hashes under the same
inherited-provider boundary.
