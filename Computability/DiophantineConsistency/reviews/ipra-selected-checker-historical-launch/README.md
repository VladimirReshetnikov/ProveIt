# Prepared selected-checker historical paired launcher

`launch-historical-pair.sh` fills the corrected independently reviewed runbook
with the observed matched parent and separately passed author and workflow
audits. It pins all three verifier terminal observations and rehashes all 35
inputs recorded by the final independent workflow review before the runbook's
full gates. Its SHA-256 is
`b60d836e6e65fc528304bc6d12e85573f2e40c198f1cedc426e4e714ce1fe36a`.

Both selected-checker audit receipts and terminal observations matched their
hashes and actual exit 0; all 35 reviewed inputs matched. `bash -n` and parsing
the six embedded Python blocks passed, and the run-01 output path was unused.
The runbook checks both tracked package source choices, the author direct-input
count, both audits and the original parent at launch. The preserved earlier
freezer bug and partial review are not used as a successful review.

Run from the repository root only after coordinating stable HEAD through
planning, freezing and preparation. Capture the actual outer exit and complete
output, preserve failed runs without overwriting, and require a separate
complete artifact audit after any successful coordinator result. This is
preparation only: no real paired run, current-source provenance, or inherited
external-ancestry claim follows.
