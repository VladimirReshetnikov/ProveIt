PA194SEL — simultaneous history selectors
=========================================

This is a deterministic one-tape binary machine with 194 working states,
388 transitions, an entirely zero two-way tape, initial head coordinate 0,
start state 0, and terminal label 194 (not counted). Native start is 74;
native halt is 254. The tables and their dense/native conjugacy are frozen.

Dense SHA-256:
5121f0b417ea025af140804b59e50a9d2fc3c461612e98b2f0ac86742c76a75b
Native SHA-256:
98b02254c280a54a763d278841bc33ab8d162f367247c01fa8d2d7cd28acbee1

Eight native rows change from the pinned primary PA194. The old pairs
(12,38) and (127,124) are merged at checkpoints; old labels 38 and 124
become selectors that inspect the bit just written to the left. Unchanged
providers reproduce the old action in three steps. The other cases take
one step. This is a recurring control change, with no state saving.

The complete written relative proof is report/selector_proof.tex, included
in the main report. Quantifier-free induction proves in iPRA:
  old halts by t  ==> new halts by 3*t;
  new halts by t  ==> old halts by t.
Consequently both halting and nonhalting are equivalent in iPRA. Any
absolute calibration of the pinned primary transfers directly. The
repository's open primary calibration to Con(PA) remains open here.
The Python checkers check all finite table premises of this mathematical
proof; no new Lean kernel build is claimed.

Run the release verifier from the archive root:
  python3 verify.py --full

Individual commands, from this directory:
  python3 build.py
  python3 verification/check.py
  python3 verification/independent_check.py --old inputs/primary.native.tm --new machine/pa194sel.native.tm --output verification/independent.json

The literal startup check is 58,208 steps to native state 84, head -2,
with exactly the same complete tape as the primary after 58,154 steps.
The all-time theorem follows from the local proof and induction, not
from extrapolation of this finite trace.
