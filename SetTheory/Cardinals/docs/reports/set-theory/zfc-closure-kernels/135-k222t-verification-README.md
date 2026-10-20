# Fresh portable verification

`full_replay.json` records the successful clean run of the supplied
`reproduce.py --full` driver. All 13 subprocess phases returned zero.
The run reconstructed both source programs and both literal tables,
checked their finite logical and emitter certificates, simulated both
initializations by independent methods, and freshly rederived all 5,956
and 6,167 guarded unbounded runtime cases. It completed in approximately
211 seconds on the preparation environment; runtime is hardware-dependent.

`logs/` contains the unedited phase output. The fresh mathematical receipts
are in the corresponding `evidence/conditional/`, `evidence/seed/`, and
`evidence/logic/` directories. In particular, `runtime_cases.json` contains
the full per-guard affine duration, displacement, and rule-count record.
The successful runtime receipts bind these case files, the source, the
literal table, and the checker components by SHA-256.

The separate `runtime_receipt_audit.json` files in both candidate evidence
directories record the stricter independent stored-evidence audit. That
audit additionally checks source-prescribed head displacement and every
checker/case-file hash. Its scope is evidence integrity, not a second
derivation of the unbounded symbolic proofs.

`full_replay_input_manifest.json` is the exact inventory checked at the
start of the full run; its hash appears in `full_replay.json`. The final
archive inventory differs because the new receipts, CSV tables, and this
verification directory were added, and the PDF pagination/metadata were
finished after that run. `proof_input_binding.json` independently records
that the reproduction driver, proof/checker code, original machine/source
files, and frozen predecessor inputs remained byte-identical. The final
top-level `MANIFEST.json` and `SHA256SUMS` cover the delivered artifact.

These are executable mathematical checks and ordinary proof arguments.
They are not a new Rocq or Lean kernel endpoint.
