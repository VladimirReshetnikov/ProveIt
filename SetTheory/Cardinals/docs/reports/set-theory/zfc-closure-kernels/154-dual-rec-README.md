# Verification receipts and their scope

* `runtime_copy.json` / `runtime_copy_cases.json` and the corresponding
  cache files are fresh all-natural symbolic primitive proofs for the exact
  published native table/source hashes. They were rederived during this work.
* The baseline replay and audit receipts record a fresh replay of the pinned
  K219 construction and its complete primitive proof.
* `portable_quick_replay.json` records the successful portable core replay
  before final report and research-directory assembly. Its smaller manifest
  census describes that earlier assembly, not the final ZIP inventory.
  The core table/source/driver identities have not changed.
* `independent_portability_audit.json` independently reconstructs those same
  exact tables from a different working directory, including spaces in paths,
  reruns complete blank initialization, and audits stored runtime receipts.
  It does not claim another fresh symbolic derivation.
* `root_research_portability.json` covers the documented representative
  research-script imports and smoke commands, not exhaustive research replay.
* PDF layout review and component inventory checks are recorded separately.

The final `MANIFEST.json` is the authoritative complete file inventory.
Run `portable/reproduce.py` to check that inventory and reconstruct the
concrete variants. The default rederives their symbolic primitive proofs;
`--quick` audits their stored proof receipts. Neither mode checks the prose
calibration in a proof-assistant kernel.
