# Candidate: 42-variable quartic with a positive V coordinate

This is an **unproved candidate**, not a new equivalence with ZFC consistency.
Starting from the pinned 43-variable candidate, `generate.py` replaces its two
positive coordinates `vPositive` and `vNegative`, used through their difference
`V`, by the single positive coordinate `vValueVariable`. The resulting circuit
has 42 positive inputs and 174 live arithmetic rows; it has the same four fixed
ports and 33 squared residuals as its parent.

`verify_substitution.py` checks the exact polynomial identity for every parent
residual under `vPositive = vValueVariable + 1`, `vNegative = 1`, leaving all
other coordinates and ports unchanged. Thus every positive candidate solution
embeds into a positive parent solution. This check does **not** show the
converse: a parent solution may have a negative signed V, and positivity cannot
be assumed from the identity. A separate existence-preserving witness
construction or other orientation argument is required. Existing auxiliary
witness construction lemmas explicitly assume an orientation equality and do not
alone discharge that condition.

`verify_degree.py` performs exact integer polynomial arithmetic on the residuals
and checks degree four after the positive shift; this finite computation is not
a Lean degree theorem. Its leading homogeneous term argument uses a residual
with a nonzero port-independent top-degree coefficient, so squaring and summing
cannot cancel its leading degree over the reals. The original 43-variable
candidate's model and native proof replays have separate status and provider
qualifications; no Lean zero-set or native iPRA theorem is asserted here.

Run `python generate.py` followed by `python verify_substitution.py` from this
directory; the generator pins its parent JSON and the verifiers pin both
candidate JSON files. The candidate SHA-256 is
`98e9d64a3c15b168c9a0cbcd813abd05d11cea627c5b8c9de004d493ed9453f3`.
