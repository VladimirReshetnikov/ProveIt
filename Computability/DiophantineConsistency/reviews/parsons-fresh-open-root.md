# Fresh-variable opening below the counterexample rule

`ParsonsFreshOpen.fresh_open` shifts every free variable of an existential
rule's cut-free premise, then uses height-preserving universal inversion to
open a selected nonprincipal universal at the newly freed variable `&0`.
It produces an actual cut-free derivation with the opened formula `A.free`
and the shifted remaining context, of strictly smaller height than the
original existential conclusion. This is the form needed to generalize an
opened guard after a recursive argument.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. Its
axiom report lists `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-fresh-open-replay/FILES.json) has SHA-256
`6223fe02728bb5257f4abac04b7dc2f1a15af14b338dfc24e7a33998d38a0e54`.
The direct `ParsonsAllInvert` source hash
`5ba857ee492335e85d94abab70b5a93434294af088afe58784d71937323e11a8`
matches its frozen snapshot, and its object hash is
`5d3ec89d2e4f17bca1995e3c58f245b295f8eb65ee15a4388b28bc4acb0151c0`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

This proof only opens the side and preserves the height bound. It does not
supply the recursive cases, normalize a general Π₂ guard, prove conservation,
or establish the desired HA-provability result.

## Independent root replay

A third build at `/tmp/parsons-fresh-open-build-xw055cz7` passed; source,
object and complete-log hashes match both author runs. The inversion provider
matches the independently rebuilt object. The [independent artifacts](parsons-fresh-open-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
