# Nine-variable peer replay: stages 61–65

The bounded peer replay compiled `IPRAErasedInductionShape`,
`IPRAReferenceCloseFamily`, `IPRAReferenceEqualityTools`,
`IPRAErasedSuccessorShape` and `IPRAReferencePredecessor`. For each stage the
author and peer source hashes, output object hashes, complete compiler output,
selected direct dependencies and recorded candidate/companion guards match
after normalizing the two overlay-root paths. Both guarded ledger checks
pass. This is a scoped exact object match for these five stages, not for the
104-stage chain as a whole.

[`audit.py`](audit.py) checks both live ledgers and the per-stage records.
[`capture.py`](capture.py) retains source snapshots, receipts, dependency
listings, compiler output, audit output and terminal receipt under
[`observations`](observations/). Repeating the audit requires the live `/tmp`
overlays. Guards are sampled at recorded boundaries; earlier project,
package-transitive and dynamic ancestry remains inherited. These stages do
not include either nine-variable endpoint.
