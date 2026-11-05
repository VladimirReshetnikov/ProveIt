# Uncompiled syntax draft for the five-norm, 38-witness seed

`SharingSeed38.lean` is generated from the pinned, externally reviewed
`nine-sharing-quartic65-norm38-candidate/seed.json`. It defines 29 residuals
over `Expr (Fin 39)`, including the distinguished input at coordinate 0,
and their sum of squares. Four ring coefficients are parameters indexed as
beta, K0, MC, MF. The first residual is singled out for a proposed
normalization proof; the other 28 include materialization constraints and five
norm constraints in the exact seed order. Candidate statements assert weighted
degree at most four, polynomial degree at most four, and all-input
normalization when beta is positive.

**This file has not been compiled.** Its declarations and tactic scripts are
unverified; `check.py` and `result.json` only compare rendered source text to
the pinned JSON and check the external syntactic-degree bound. The generator
and checker use the same rendering convention, so this is not an independent
Lean parser or proof. Run `python3 -I -S -B check.py` for that limited check.

There is no all-model zero bridge or iPRA endpoint here. The seed constraints
must be linked in Lean to the five norms and current source expression, using
the ordered-ring and positivity hypotheses of the existing norm theorem and
proving fixed-port values arise from the model's natural semiring. An
all-model forward assignment and reverse reconstruction, the Jones
instantiation, and consistency endpoint remain separate work. The external
candidate's fixed bytes and source correspondence are not established by this
Lean source.
