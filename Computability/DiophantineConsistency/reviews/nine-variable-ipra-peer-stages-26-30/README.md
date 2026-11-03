# Nine-variable peer replay: stages 26–30

The bounded peer replay compiled `NaturalSimplifier`, `WitnessCompaction`,
`CompactedJonesSyntax`, `ComputationRepresentation` and `ScalarPRCode`.
For each of these five stages, the author and peer source hashes, output
object hashes, complete compiler output, selected direct dependencies and
their recorded candidate/companion guards match after normalizing the two
overlay-root paths. All five compiler logs are empty. Both guarded ledger
checks pass. This is a scoped exact object match for these stages, not for
the 104-stage chain as a whole.

[`audit.py`](audit.py) checks both live ledgers and the per-stage records.
[`capture.py`](capture.py) retains source snapshots, receipts, dependency
listings, compiler output, audit output and terminal receipt under
[`observations`](observations/). Repeating the audit requires the live `/tmp`
overlays. These checks are sampled at recorded boundaries; earlier project,
package-transitive and dynamic ancestry remains inherited, and neither
nine-variable endpoint is part of these five stages.
