# Compact release-tool review handoff

Copy this entire directory unchanged to `release-tool-review/` in the release. `EVIDENCE_MANIFEST.json` lists every handoff file except itself, with byte lengths and SHA-256 hashes. It is not a replacement for the final whole-release manifest.

## Start here

- `RELEASE_TOOLS_REVIEW.md`: outcome, exact final pins, demonstrated defects, fixes, qualifications and coverage
- `REVIEW_RECEIPT.json`: compact machine-readable final result
- `TEST_RESULTS.json` and `SUMMARY.json`: 142 original standard checks and original input pins
- `SNAPSHOT_PROBES.json` and `RELEASE_RACE_PROBES.json`: seven original structural/race demonstrations
- `revised/REGRESSION_RESULTS.json` and `revised/SUMMARY.json`: 42 passing post-fix checks
- `revised/build/BUILD_RECEIPT.json` and `revised/REFERENCE_BUILD_RECEIPT.json`: final-source fresh hostile build versus final draft7; identical PDF, text and 22 page PNGs
- `revised/build/BUILD_DEPENDENCIES.json`: installed executable and recorded TeX/font-map hashes for the final fresh build
- `APPLIED_HARDENING.patch`: actual original-to-final source changes

## Check sources and reproduction

The four independent check sources are `audit_release_tools.py`, `probe_build_snapshot.py`, `probe_release_races.py`, and `regress_hardening.py`. They contain no scientific imports or executions. Their original absolute path constants are retained for exact provenance; do not run them unchanged against an unrelated working directory.

To repeat the checks elsewhere, work only in a fresh external scratch directory, copy the check source there, and change its explicit path constants to your copied release and scratch/reference locations. Invoke the copies with `python3 -I -S -B`. Do not point mutation cases at the original release. The harnesses make further copies for mutations; the two probe scripts deliberately emulate boundary interleavings using the inspected release tool's functions. The regression's reference build must have the same manuscript pins as the source being tested. A normal isolated reference build followed by the hostile build supplies that comparison; preserve both receipts.

For the original 142-check snapshot, `SOURCE_SNAPSHOT.json` supplies the exact original file inventory. All unchanged science, dependency and audit bytes are in the final release. `baseline/` carries the five files that differed between that original snapshot and the final release: the old README, old manuscript and its pin JSON, and original builder and release checker. Reconstruct a scratch baseline by taking exactly the snapshot's listed files from the final release, then overlaying these baseline files, and verify every length/hash before testing. Extra later release files must not be included in that baseline. The initial probes require the initial harness's scratch manifest, created during its successful run.

For the final 42-check regression, use the final reviewed tool and manuscript hashes in `REVIEW_RECEIPT.json`. Other top-level review/build evidence was still being assembled when its scratch archive was made, so the recorded 123-file test ZIP is a snapshot-specific packaging result, not the final distributed archive. The equivalent tests on a later complete release will intentionally have a different file count and manifest/ZIP hash. `revised/SOURCE_SNAPSHOT.json` records the exact tested inventory.

A final release check is still required after integrating this handoff: create the whole-release manifest externally, install its bytes intentionally, verify with its independently retained SHA-256, then archive to a fresh external path. Only exit code zero plus PASS establishes successful archive completion; failed partial archives are retained.

## Deliberately omitted

Large scratch release copies, test ZIPs, page PNGs, intentionally corrupted test artifacts, poisoned environment fixtures, and duplicated full transcripts are omitted. The relevant hashes, build dependency inventory, per-check outcomes/output tails and executed checker source are retained. Detailed originals remain in the review workspace. The whole-release `Report59.pdf`, scientific/audit files and final release tools are not duplicated here.
