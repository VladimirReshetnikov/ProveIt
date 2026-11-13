# Independent incremented mixed-mask decoder audit

The read-only [audit](audit.py) of `116ab88a4c` actually exited 0 in session
49564; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/object/log chains, complete shared window overlays,
the two copied parent seeds and independent parent-audit reruns, direct
imports and recorded child and outer exits. Each side reports the expected
theorem with Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`,
without warnings or `sorryAx`. No Lean compile was rerun.

For model naturals m, N, C and MC, the theorem explicitly assumes positive
m and N, `MC < 2^(67m)`, a three-way classification of every block digit,
origin digit `2^67−2`, `1 ≤ C`, and
`NoCarry (C−1) (MC * rep(67m,N) + 1)`. It concludes the zero digit of C
is 1 and every digit below mN is at most 3. The mask classification and
global no-carry are hypotheses, not results about the actual graph. No full
tuple binding, coefficient-mass proof, temporal support, machine simulation,
checker calibration or PRA proof is claimed.

The source packet retains the failed first exploratory attempt separately.
The window provider lacks a complete printed axiom inventory; Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain.
Resource measurements are sampled, not whole-tree quotas.
