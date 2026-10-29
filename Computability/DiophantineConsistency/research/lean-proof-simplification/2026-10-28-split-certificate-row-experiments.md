# Split certificate row-proof experiments

The 22 private `rowIdentity` proofs in `SplitCertificate59.lean` each restate
support, coefficient and source expressions before proving the corresponding
ring identity. Two generated alternatives sought to remove that repetition:

- **Direct unfolding** used the same `simp` and `ring` proof for each row,
  reducing the generated source from 866 to 690 lines. It was interrupted
  after a process observation of approximately 123 seconds of user CPU.
- **Explicit quadratic supports** retained the per-row quadratic support fact
  but unfolded the other definitions in the common proof, reducing the source
  to 734 lines. It was terminated after 54.35 seconds of user CPU, as recorded
  by `/usr/bin/time`.

A separate earlier build of the unchanged target used 22.66 seconds of user
CPU. Both experiments exceeded that value before termination, but **neither
candidate completed**, so those numbers are lower bounds, not completed
benchmarks or proof validation. The baseline was not paired under identical
load; other Lean work was running. Both candidates regenerated
`SplitGeometry59.lean` byte-for-byte, but neither received production-client or
interface checks. The intermediate all-row output object is not evidence of a
successful candidate build.

A one-row preliminary attempt failed on a support-membership goal; adding
`quadraticIndices` and `activePair` to simplification let that one-row variant
compile. This does not establish that either all-row proof compiles. The
recorded target source and intended direct `SplitGeometry59` provider match the
prior successful baseline build. The interrupted runs have no per-run input
hash receipts, so their provider identity is not independently pinned;
transitive inputs remain cached. The direct attempt's
CPU observation was noted manually and has no saved time receipt. The controlled
attempt's termination receipt, the prior baseline receipt, source and generator
snapshots, pinned JSON inputs and partial logs are in the
[evidence bundle](../../reviews/lean-proof-simplification-20261028-split-certificate-row-evidence/BUNDLE.json).
