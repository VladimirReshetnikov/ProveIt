Independent audit of the paired-sign and square-anchored factorial-radius quartics

Main proof audit: REVIEW.md
Independent verifier: audit_paired_independent.py (Python standard library only)
Negative controls: check_negative_controls.py (imports only the independent verifier)

Portable replay, replacing PACKET with the directory containing source/ and the two endpoints:

python audit_paired_independent.py --baseline PACKET/source --candidate PACKET/paired --output NEW_PAIRED_AUDIT
python audit_paired_independent.py --baseline PACKET/source --candidate PACKET/squared_paired --output NEW_SQUARED_AUDIT --squared-radius
python check_negative_controls.py --baseline PACKET/source --candidate PACKET/squared_paired --output NEW_SQUARED_AUDIT/NEGATIVE_CONTROLS.json --squared-radius

The same commands with python -O check that no proof obligation depends on Python assertions.
--baseline also accepts PACKET itself or the original round-14 release root.
The frozen mixed-source and domain-certificate canonical SHA-256 values are pinned.

Every endpoint audit directory contains its exact replay, independent pre-power bound DAG,
complete 63-guard disposition ledger, and negative-control results. The independent bound DAG
is separate from the producer's fresh presemantic certificate; both are verified.

This audit proves the stated local transformation arguments and checks all finite algebra.
The complete incoming literal-source/C222 calibration and simultaneous signed-Pell theorem
are substantive imported ordinary-proof dependencies, not independently certified here.
This scope limit is stronger than merely not running a new formal-kernel proof.
See REVIEW.md Section 10 for the exact reading ledger and dependency risks.
