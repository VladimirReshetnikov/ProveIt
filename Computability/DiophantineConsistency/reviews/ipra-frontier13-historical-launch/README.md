# Prepared joint 13-variable historical paired launcher

`launch-historical-pair.sh` fills the independently reviewed runbook with the
observed matched parent and separately passed author and workflow audits. It
also pins all three verifier terminal observations and rehashes all 32 inputs
recorded by the independent workflow review before the runbook's full gates.
The launcher SHA-256 is
`26ea6b2e8811f23033afcabc8d9a27f9cc70023cd8c048bd45871e2f6dd4bb00`.

Both 13-variable audit receipts and terminal observations matched their hashes
and actual exit 0; all 32 reviewed inputs matched. `bash -n` and parsing the
six embedded Python blocks passed, and the run-01 output path was unused.
The runbook checks the exact tracked package source choices, both independent
audits, the author direct-input count, and the original parent at launch.

Run from the repository root only after coordinating stable HEAD through
planning, freezing and preparation. Capture the actual outer exit and complete
output, preserve failed runs without overwriting, and require a separate
complete artifact audit after any successful coordinator result. This is
preparation only: no real paired run, current-source provenance, or inherited
external-ancestry claim follows.
