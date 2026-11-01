# The 42-variable quartic equation with a positive V coordinate

The [base-10 equation](../../equation4-42.pdf) has 42 separately named positive
integer unknowns and a 174-operation circuit. The no-premise Lean theorem
[`IPRAQV42Native.literal_equivalence`](../../Lean/DiophantineConsistency/IPRAQV42Native.lean)
asserts a derivation in the project's native intuitionistic PRA candidate: the
fixed-port equation has no positive zero if and only if Foundation's particular
mapped ZFC refutation predicate is negated. Its [focused paired replay](../../reviews/adaptive-qv42-native-final-replay/README.md)
matched five modules and rebuilt all three accepted sign-transport objects. The
runs combine a 31-native primary provider with missing objects from a conditional
quartic provider; their overlapping transitive ancestry, external packages and
dynamic imports remain inherited. This historical result is not a fully
authenticated current-source closure.

Starting from the pinned 43-variable graph, `generate.py` replaces its positive
pair `vPositive`, `vNegative`, used through their difference `V`, by the single
positive coordinate `vValueVariable`. `verify_substitution.py` checks all 33
parent residuals under `vPositive = vValueVariable + 1` and `vNegative = 1`
as exact polynomials. The identity alone supplies only the candidate-to-parent
solution map; it does not orient every parent zero.

The Lean proof constructs a suitably oriented witness from a halting run. The
[oriented-witness model theorem](../../reviews/adaptive-qv42-oriented-replay/README.md)
relates positive 42-variable zeros to positive 43-variable zeros with the
explicit sign `v 26 < v 25`. The [conditional native bridge](../../reviews/adaptive-qv42-conditional-native-replay/README.md)
requires a halting-to-oriented-witness premise; the final endpoint discharges
it via the constructed auxiliary seed and the checked sign-preserving
extensions. It does not claim pointwise orientation of every parent zero.

`verify_degree.py` checks exact degree four after the positive shift using
sparse integer polynomials. A residual has a nonzero port-independent leading
coefficient, so the squared residuals cannot cancel their highest degree over
the reals. This finite computation is not a Lean degree theorem; no global
minimality is claimed.

Run `python generate.py` followed by `python verify_substitution.py`; the
scripts pin their graph inputs. Candidate SHA-256:
`98e9d64a3c15b168c9a0cbcd813abd05d11cea627c5b8c9de004d493ed9453f3`.
