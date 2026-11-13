# Lean comparison after the q³ substitution

`QCube92Model.zero_iff_transformed` proves, in **every model of IΣ₁**, that
the 92-graph is zero at a valuation if and only if the checked 94-graph is
zero after replacing the old `Y` coordinate by `q³s`. The ports are arbitrary
natural numbers interpreted as integer constants. The theorem has no
positivity hypothesis on the inputs or β: `cube_ne_zero` proves `q³ ≠ 0` in
the model's ordered difference ring, and the comparison uses nonnegativity
of the three residual squares. The valuation includes nonstandard model
elements.

This is an identity after a specified valuation transformation. It does not
prove that every positive old zero has a positive quotient witness; that is a
separate existence and provider-compatibility obligation. It also does not
identify a compressed coefficient file or PDF inside Lean, or establish an
iPRA derivation.

The recorded author check `observations/model-attempt01/` exited 0 in 10.2
seconds without warnings or `sorryAx`. All three named reports contain only
the Lean metatheory axioms `[propext, Classical.choice, Quot.sound]`. Its
source and runner hashes are
`4f3b882c9ff4fa10672437797864bb64bfd4bb4355a7b837a5ee3f84c799acea` and
`51e414cc6f3e7d7f8cf2e58d2eeeec1eb687a6f0e71807a254e1b1a2abb80916`.
It imports the exact author object from `attempt05` and the previously used
94-graph provider. The runner traversed 75 selected provider files and
recorded no changes; symlinked directories and full project, package and
dynamic ancestry are outside that inventory. Five resource samples recorded
at most one Lean process and a minimum 18,488,796 KiB MemAvailable; brief
inter-sample overlaps or memory dips remain possible. This is a single-author
check, not an independent replay.

Replay against the recorded provider paths using an unused attempt number:

```sh
ATTEMPT=attempt02 python3 run-model.py
```
