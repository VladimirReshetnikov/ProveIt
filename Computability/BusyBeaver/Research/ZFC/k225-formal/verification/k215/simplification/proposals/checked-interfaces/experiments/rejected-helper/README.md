# Rejected guarded-subtype abstraction

These are the actual proposed helper and target sources from the initial
experiment. The target shrank from 50,827 to 50,555 bytes, but the new helper
cost 1,176 bytes: a net increase of 904 bytes. This variant is retained only
for source-size review and is excluded from the accepted replay.

The generic helper was checked in an isolated experiment. This directory does
not supply a separate fresh replay receipt for the helper-and-target pair.
The accepted five-proof-body patch and its fresh Lean 4.32.0 evidence are under
`../../lean-normalization/`. Use that version for the proposed integration.
