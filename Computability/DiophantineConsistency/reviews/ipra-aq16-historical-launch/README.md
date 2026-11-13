# Prepared AQ16 historical paired launcher

`launch-historical-pair.sh` fills the reviewed runbook's parent observation,
parent pair, AQ16 workflow-audit, and AQ16 guarded-author audit paths and
recorded hashes. It also adds SHA-256 pins for all three independent verifier
terminal observations, before the runbook's existing authentication gate.
The launcher SHA-256 is
`1b118c19ab846506891f5b1d881c58add1acad99452955359ad5eb2da15b3989`.

`bash -n` and parsing all six embedded Python blocks passed. Both AQ16 audit
receipts and terminal observations matched their recorded hashes and exit 0;
all 84 inputs pinned by the independent workflow review still matched. The
run-01 output path did not exist at this check. The runbook still performs
the full parent, workflow and author-audit authentication at launch.

Run from the repository root only after coordinating stable HEAD through
planning, freezing and preparation. Capture the actual outer exit and full
output, retain failed runs without overwriting, and obtain a separate complete
artifact audit after any successful coordinator result. This is preparation,
not a matched AQ16 replay or a current-source/external-ancestry claim.
