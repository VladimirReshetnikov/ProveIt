# Source review: halt, Pell seeds and first carrier

This is an independent **source-only** review, without a Lean replay or full
provider-closure audit. The reviewed final
`compact44-halt-first-seed-prototype/CompactHaltFirstSeed.lean` has SHA-256
`971e0f7f5da111dbaf90daf27cb10b76afe935c2c1c814410f2d53a32bfc62f7`.

`halt_first_seed` assumes only the model-internal halt of decimal215 at `T`,
in a model of `IΣ₁`. Its output contains the selected Boolean controller,
its explicit support bounds, the full symbolic compact packing, and an
explicit proof that the same pulsed word `X` is model-Σ₁-definable. Under a
local instance binder for that *already-proved* definability it preserves
the rank congruence and a single positive shifted-transport witness `z`,
including `q*w=Exp.exp R` and the shifted transport equation. It then
returns positive `sY,n,eta,zeta,gamma` with the outer `SeedRelations` and
size bound, auxiliary `AuxData u R sY`, and
`FirstData K N s X sY n eta zeta z`.

The proof first unpacks a single halt/Pell/transport result, then unpacks its
outer seed. It passes precisely those unpacked `sY,n,eta,zeta,gamma` and the
same `z`, word, kernel, length, stride and transport equations to
`first_from_transport`. The resulting first-carrier `r` is existential
inside `FirstData`; its equation uses the same outer parameters and `z`.
`AuxData` separately existentially quantifies its auxiliary Pell variables,
but shares the very same `u,R,sY` (hence `Y`, `a`, and `c`) with the outer
seed. The theorem does not assert that the auxiliary witness is a previously
separately chosen one, nor does it need `r` to depend on an auxiliary
witness. Quantifier placement in the statement supports the stated scope.

The first carrier relation is an additive model-natural identity, not by
itself the evaluated exact graph factor. Nor does this theorem construct the
adaptive main gamma, all positive graph coordinates, a free-J graph zero,
retained-byte/PDF equality, or an iPRA derivation. The author's successful
build and its guard evidence remain separate; this review does not establish
a paired replay or authenticate complete transitive, package or dynamic
provider ancestry.
