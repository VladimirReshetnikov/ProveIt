# Verification receipts

`full_replay/` is the unedited output of the completed packaged default replay. Its final status is `FULL_238_REPLAY_PASS`, with both universal proofs executed. The construction, source data, mathematical checker scripts and runtime engine used in that replay are the exact ones delivered in this package.

The replay began while the report was still being typeset. Its `manifest_files_checked: 83` records that stage's input manifest, retained as `replay_input_manifest.txt`; it is not the file count of the final distribution. Subsequent changes added documentation and evidence and corrected prose in the source-bisimulation section. They did not change either machine, either source list, the construction algorithm, or any executed proof checker. `release_checks.json` checks these identities against the fresh receipts. The root `SHA256SUMS` covers the final delivered files, including the finished report.

The universal runtime drivers share the unchanged attributed `verification/symbolic_runtime.py` engine and its helper. Their different roles are a direct all-frame proof for the new table and an old-table all-frame proof with the extra state-169 guard. They are not independent universal proof engines. Separate source-control, open-tape, finite-window, initialization and adversarial audits are included at their stated scope.

The files under `full_replay/` contain mathematical proof-construction output, not a trace of an infinite Turing-machine computation and not a proof-assistant kernel certificate. The report explains each induction rule and the inherited logical calibration.
