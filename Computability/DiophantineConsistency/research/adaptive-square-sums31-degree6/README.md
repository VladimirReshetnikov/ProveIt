# Candidate: 31-variable degree-six equation with a positive V coordinate

The [base-10 candidate display](../../equation6-31.pdf) is an **unproved candidate**, not a new equivalence with ZFC consistency.
Starting from the pinned 32-variable degree-six candidate, `generate.py` replaces
its two positive coordinates `vPositive` and `vNegative`, used through their
difference `V`, by the single positive coordinate `vValueVariable`. The
resulting circuit has 31 positive inputs and 141 live arithmetic rows; it has
the same four fixed ports and 22 squared residuals as its parent.

`verify_substitution.py` checks the exact polynomial identity for every parent
residual under `vPositive = vValueVariable + 1`, `vNegative = 1`, leaving all
other coordinates and ports unchanged. Thus every positive candidate solution
embeds into a positive parent solution. This check does **not** show the
converse: a parent solution may have a negative signed V, and positivity cannot
be assumed from the identity. A separate existence-preserving witness
construction or other orientation argument is required. Existing auxiliary
witness construction lemmas explicitly assume an orientation equality and do
not alone discharge that condition.

A Lean [oriented-witness theorem](../../Lean/DiophantineConsistency/AdaptiveAQ31.lean)
now proves that candidate positive solutions correspond exactly to positive
parent solutions with `v 24 < v 23`, for arbitrary integer ports in IΣ₁
models. Its [focused paired replay](../../reviews/adaptive-aq31-oriented-replay/README.md)
matched; it does not establish existence of an oriented parent solution.

A separate [conditional shifted no-zero theorem](../../reviews/adaptive-aq31-conditional-nozero-replay/README.md)
shows the 31- and 32-variable no-zero statements are equivalent if existence
of a positive parent zero implies existence of an oriented one. The proof does
not require orienting every individual parent zero; the remaining task is to
discharge this existence hypothesis for the fixed ports.

A [conditional native iPRA bridge](../../reviews/adaptive-aq31-conditional-native-replay/README.md)
now reduces the desired fixed-port result to the explicit all-model assertion
that a halting run yields an oriented positive 32-variable witness. This
assertion is not yet discharged by the conditional bridge.

`verify_degree.py` performs exact integer polynomial arithmetic on the residuals
and checks degree six after the positive shift; this finite computation is not
a Lean degree theorem. Its leading homogeneous term argument uses a residual
with a nonzero port-independent top-degree coefficient, so squaring and summing
cannot cancel its leading degree over the reals. The original 32-variable
candidate's model and native proof replays have separate status and provider
qualifications; no unconditional Lean zero-set or native iPRA theorem is asserted here.

Run `python generate.py` followed by `python verify_substitution.py` from this
directory; the generator pins its parent JSON and the verifiers pin both
candidate JSON files. The candidate SHA-256 is
`a90ab59a3ab1b3e9b04c2b962ea79c666a3c2dc90e6941c73f5180ab73c5ee67`.
