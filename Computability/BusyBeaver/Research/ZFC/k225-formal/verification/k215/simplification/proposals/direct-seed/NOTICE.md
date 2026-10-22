# Attribution and evidence scope

This packet studies and refactors the ProveIt sources at commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`. Original machines, calculi, encodings,
proofs, model constructions, and generators belong to the existing project and
its credited sources. `LICENSE.ProveIt` reproduces the project's MIT No Attribution
license; inherited source headers are retained.

Specific antecedents are credited in the report:

- The shared six-goal implication basis preserved from branch revision
  `49e99c5b7cc6c2e164331961de28bad3904361fd` in the phase-twelve upstream-merge inputs.
- The `sharing-interfaces/calculus/DIRECT_FULL_SEED.md` proposal and the existing
  Rocq `rocq224/src/Complete222.v` construction.
- The existing `checked-transport/rocq_seed_rank` arbitrary-state completeness
  proposal. The included Rocq component is an API-preserving alternative.

The new work consists of implementation and integration at the selected baseline,
maintained-producer synchronization, compatibility checks, mathematical review,
source measurements, reproducible component checks, and this report. No claim of
a newly discovered axiom basis, smaller machine, new internal ZFC derivation, or
full machine-specific endpoint replay is made.

Recorded source hashes, compiler logs, assumption reports and object hashes are
evidence for the explicit completed runs. Absolute build paths in those receipts
describe the original run; the reproduction scripts resolve their inputs relative
to the extracted packet and write into caller-selected fresh output directories.
Run times are incidental observations, not controlled comparative benchmarks.
