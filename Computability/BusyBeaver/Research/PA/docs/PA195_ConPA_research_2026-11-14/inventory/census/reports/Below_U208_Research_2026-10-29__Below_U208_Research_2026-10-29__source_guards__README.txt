Blank-calibrated source reachability audit
=========================================
The source-level category invariant is independently checked for both current
209-state source layouts. This is a prerequisite for sound unreachable-branch
pruning, not an accepted smaller machine by itself.

Run Python3.10+, standard library:
 python3 -B generate.py inputs/compatibility.sites.json /tmp/certificate.json
 python3 -B check.py inputs/compatibility.sites.json /tmp/certificate.json --other inputs/joint.sites.json
 python3 -O -B check.py inputs/compatibility.sites.json certificate.json --other inputs/joint.sites.json
 python3 -B negative.py
 python3 -O -B negative.py

The generator uses subtree-interval target resolution; the independent checker
uses binary-prefix arithmetic and tests every inductive successor inclusion.
See PROOF.md for transfer soundness, the exact startup premise and limits.

Inputs are copied from ProveIt commit343da82d7384d10ec9fd1c17361fc923b2d1d117:
U209_ConPA_Compatibility_2026-10-29/source/u209.sites.json and
U209_ConPA_Joint_2026-10-29/machine/sites.json, inside their supplied archives.
Both remain attributed to their incoming constructions. No source instruction
or machine transition is changed by this audit. No kernel certificate claimed.
