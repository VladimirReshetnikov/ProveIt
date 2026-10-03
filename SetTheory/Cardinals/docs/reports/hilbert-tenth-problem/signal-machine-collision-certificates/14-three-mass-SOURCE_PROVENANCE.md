# Source and verification provenance

The frozen native generator is `code/three_mass_collision_generator.py`, preserved byte for byte with SHA-256:

    14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52

Its finite source tables generate the cycle, inverse-merge and invalid-decrement-trap examples. These are test fixtures, not an expanded universal program. The report's fixed universal instance uses the classical source-existence theorem cited in its bibliography.

`code/certificate.py` and `code/checker.py` include the audited physical-clock option: omitted or explicit `clock_scale=1` for native or spatially blocked ticks, and `clock_scale=4` for internal four-phase ticks. The two `code/legacy/` snapshots are the pre-clock certificate producer and checker. They are retained only for serialized byte-compatibility regression. Their SHA-256 values are:

- Legacy producer: `bfc7588058b68ce773a91af8ca0730647cb3c9cb1821dda5928a534aa33d97ed`
- Legacy checker: `9068dd7a87c2e5ee001b957ea2bc0483b625fe155d14cf610261c8a4e06f0165`

`code/radius_one.py` is the coordinate-preserving four-phase wrapper with strict public input checks. `code/spatial_radius_one.py` is the separately audited time-preserving four-site wrapper. Both use immutable snapshots of the native transition descriptors. Spatial offset labels and temporal phase labels are different encodings.

The release test harnesses use package-relative source discovery and explicit output directories in place of construction-workspace paths. Their exact published bytes are identified by `SHA256SUMS` and `receipts/replay-summary.json`. These packaging changes do not modify the frozen generator or mathematical rule. The spatial wrapper's implementation is byte-identical to its audited source; its test harness has only a redundant workspace-specific fallback path removed.

Published receipts were freshly produced by `replay.sh` against this packaged revision. `receipts/replay-summary.json` records every executed Python source hash and all 16 byte-identical example exports. Source hashes within individual receipts refer to the names printed there; older labels such as `certificate_snapshot.py` and `ca_snapshot.py` in a test implementation map to the packaged `certificate.py` and `three_mass_collision_generator.py`. Elapsed-time fields are measurements and may differ on replay. Optimized receipts explicitly identify optimization level 1; all other suites run with assertions enabled.

The report contains full mathematical arguments and verified primary-source URLs. No third-party papers are redistributed. Finite tests support implementation claims; they do not prove universality, replace the all-input proofs, establish a concrete universal alphabet count, or assert literature-wide priority.
