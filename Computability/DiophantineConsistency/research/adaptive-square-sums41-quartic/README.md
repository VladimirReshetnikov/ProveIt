# The 41-variable quartic equation with a first-root quotient

The [base-10 equation](../../equation4-41.pdf) has 41 separately named positive
integer unknowns and a 170-operation circuit. The no-premise Lean theorem
[`IPRAQF41Native.literal_equivalence`](../../Lean/DiophantineConsistency/IPRAQF41Native.lean)
asserts a derivation in the project's native intuitionistic PRA candidate: the
fixed-port equation has no positive zero if and only if Foundation's particular
mapped ZFC refutation predicate is negated. Its [focused paired replay](../../reviews/adaptive-qf41-native-replay/README.md)
matched eight modules, including all six rebuilt model objects. The parent
provider combines earlier 31-native and quartic providers; overlapping
project-transitive, package-transitive and dynamic ancestry remain inherited.
This historical result is not a fully authenticated current-source closure.

Starting from the 42-variable quartic, the graph replaces its positive first
root `Z` by a positive quotient `t` (shown as `z` in the display), reconstructing
`Z = scale*t`. The first norm becomes `t² - (1+ellProduct)` and the root
binding becomes `scale*t - ZComputed`; the positive `psiSquare` coordinate and
its defining residual are removed. The resulting graph has 32 squared residuals.

`verify_substitution.py` checks the parent residual identities under
`Z=scale*t` and `psiSquare=scale²`: 31 residuals agree, the old first norm is
`scale²` times the new norm, and the removed definition vanishes. The [model
proof](../../reviews/adaptive-qf41-model-replay/README.md) supplies the missing
reverse witness construction via the checked positive-scale square-divisibility
lemma. It proves shifted no-zero equivalence with the 42-variable parent for
arbitrary integer ports in every IΣ₁ model.

`verify_degree.py` checks exact degree four after the positive shift using sparse
integer polynomials. A residual has a nonzero port-independent leading
coefficient, so the squared residuals cannot cancel their highest degree over
the reals. This finite computation is not a Lean degree theorem; no global
minimality is claimed.

Run `python generate.py` and then `python verify_substitution.py`; the scripts
pin their graph inputs. Candidate SHA-256:
`62e7851fa8cfee544f92b83ff4f422e200f10c4a45f0e236d83e1ac3f07dd239`.
