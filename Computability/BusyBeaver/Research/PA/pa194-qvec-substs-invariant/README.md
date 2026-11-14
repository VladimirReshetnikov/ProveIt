# Bounded substitution graphs along a qVec trace

`qVec_substitutions_bounded` combines the checked internal qVec trace and
actual arithmetic substitution witness ceiling. For every seed and
model-internal limit in every candidate-PRA model with an IΣ₁ arithmetic
reduct, it constructs a coded qVec history and one model element `bound`.
For every index up to that limit and every valid arithmetic formula code at
most the common qVec ceiling, the actual substitution into the indexed vector
has an arithmetic substitution graph whose existential witnesses are all
bounded by `bound` in the `bnd` sense. This includes nonstandard indices,
formulas, and vectors.

The bound is supplied by the model-level `WB` theorem; no finite code or
definable choice of it is asserted. No PAeq substitution graph, source-to-PAeq
formula translation, or full substitution-agreement invariant is provided.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-qvec-substs-invariant/check.sh
```

The final module passed a fresh suffix check against the already checked
output-ceiling theorem and retained prerequisites. Its printed axioms contain
no `sorryAx`. The full prerequisite-prefix replay remains pending.
