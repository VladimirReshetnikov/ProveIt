# Optional smooth-radix addendum

This separate packet replaces the factorial radix choice in the full
first-index-deletion counterfamily by t=4400d*2^k on the genuine
power-of-five compiler recipe. Taking k least with
t>=4 max(I,ceil(log2(K+1))) preserves every positive source equation.
The chosen radix q=2^t is singly exponential in the ordinary input
for a fixed compiler. No such claim is made about all Pell witnesses.

The frozen original packet remains unchanged:

    /workspace/shared/first-index-attack-20261003

Original manifest SHA256:
94f45847037067162dd21e77f19e8edc2cc53cb0aa9ca6642e335c5d7c21cbb4

Original full proof SHA256:
dc886e8991e32c331b9135b4ea6b3f73733656be3df6c2aa01576e1732fb83e1

Read SMOOTH_RADIX.md for the proof, ROOT_REVIEW.md for review scope,
and SOURCE_ERRATUM.md for the harmless j=2 endpoint correction in the
original packet's preliminary reduction note. That source was preserved
as frozen evidence, rather than silently corrected.

## Replays

From this packet directory:

    python3 check_smooth_radix.py --expect CHECKS.json
    python3 -O check_smooth_radix.py --expect CHECKS.json
    python3 verify_manifest.py

The checker uses script-relative paths, so absolute paths also work
from any directory. Default output is canonical JSON stdout only.
--expect compares exact bytes; optional --output only creates a fresh
external file and rejects packet paths or existing/expected outputs.
CLI_QA.json records normal/-O success and guard checks.

The exact finite checks supplement the symbolic proof. Mock modular
ports are not certified compilers; no full astronomical tuple, saved
source schedule, or upstream Python was evaluated. No public mutation,
publication or upload occurred.
