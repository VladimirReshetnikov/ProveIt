# One direction between the numerical model classes

`Code254Models.sat_encode_decode` proves semantic encoding/decoding for every
named formula in an irreflexive structure. Genuine Bottom is encoded as the
false membership atom `Rel(0,0)`; the proof accounts for that alias explicitly.
The implication case uses the numerical decoder's semantic theorem, including
its special truth code zero. No injectivity or syntactic round trip for
formulas containing Bottom is assumed.

Consequently a model of all decoded gated bundles is a model of every literal
encodable bundle. The proof preserves both original gates and rewrites the
actual axiom encoding. This is the elementary **decoded-to-encodable** direction;
the reverse implication is still unproved. The two model predicates alone are
vacuous on an empty domain. The no-refutation corollary and the adapter to
`ProfileModel.ModelsCPGIC` therefore take an explicit valuation.

Together with `Code254GIC`, both numerical model interfaces now feed the
existing first-order CP/GIC interpretation. The result does not yet supply all
quotient ZF axioms, constructibility/Choice calibration, proof enumeration,
register simulation or the final binary-machine consistency equivalence.
The numerical definitions keep the Mira-Cult/Jeff attribution in `Code254`.

All four new theorems and two interface callers passed with the explicit Lean
4.32.0 executable. Their axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`. An independent read-only review found no hypothesis or scope
defect. The checked import closure has 62 source units; the five new modules
and umbrella were rebuilt serially against the previously source-verified
57-unit cache. This was a scoped integration, not another full bootstrap build.
Exact commands, source identities, output and caller source are retained in
`results/gic-boxes-integration-verification.json`.
