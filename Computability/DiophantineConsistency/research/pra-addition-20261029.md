# Addition equations in the candidate PRA theory

`PRAAddition` proves actual Foundation derivability statements for the
candidate theory: `PRA ⊢ addZeroSentence` expresses `x+0=x`, and
`PRA ⊢ addSuccSentence` expresses `x+succ(y)=succ(x+y)`. The sentences use the
designated primitive-recursive addition, zero and successor codes and bind
all variables. Their proofs derive the equations from the composition,
projection and recursion defining equations in every equality model of the
candidate theory, then use Foundation completeness. They are not inferred
from evaluation in the standard naturals.

The final main source and focused checks compiled with Lean 4.32 using
`-M6000 -j1 -DElab.async=false` in `/tmp/pra-addition-author-p3469cav/lib`.
The complete final main log is empty and all seven axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The parent is the independently
checked merged-client provider `/tmp/pra-merged-clients-k8u39e5a/lib` with its
existing Foundation and Mathlib boundaries. Independent review and replay of
this pair remain separate.

All nine main source snapshots and logs and the one checks attempt are
preserved in the private `logs` directory. Attempts 3–5 used `sorry` as
intermediate goal-inspection probes; the final source and logs contain no
admitted proof. These addition theorems advance compatibility but do not yet
prove equivalence of the candidate theory with a standard PRA presentation,
IΣ₁ conservation, or the Diophantine consistency equivalence in PRA.
