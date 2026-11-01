# The 31-variable degree-six equation with a positive V coordinate

The [base-10 equation](../../equation6-31.pdf) has 31 separately named positive
integer unknowns and a 141-operation circuit. The no-premise Lean theorem
[`IPRAAQ31Native.literal_equivalence`](../../Lean/DiophantineConsistency/IPRAAQ31Native.lean)
asserts a derivation in the project's native intuitionistic PRA candidate: the
fixed-port equation has no positive zero if and only if Foundation's particular
mapped ZFC refutation predicate is negated. Its [focused paired replay](../../reviews/adaptive-aq31-native-final-replay/README.md)
matched 23 modules, including the no-premise endpoint. This is a historical
fixed-snapshot result with inherited project, package-transitive and dynamic
ancestry; a fully authenticated current-source closure remains open.

Starting from the pinned 32-variable degree-six graph, `generate.py` replaces
its positive pair `vPositive`, `vNegative`, used through their difference `V`,
with the single positive coordinate `vValueVariable`. `verify_substitution.py`
checks all 22 parent residuals under `vPositive = vValueVariable + 1` and
`vNegative = 1` as exact polynomials. That identity alone proves only the
candidate-to-parent solution map, since an arbitrary parent zero need not have
positive signed V.

The Lean proof instead constructs a suitable oriented witness when a halting
run exists. The [oriented-witness model theorem](../../reviews/adaptive-aq31-oriented-replay/README.md)
relates positive 31-variable zeros to positive 32-variable zeros with the
explicit sign `v 24 < v 23`. The [conditional native bridge](../../reviews/adaptive-aq31-conditional-native-replay/README.md)
requires a halting-to-oriented-witness premise; the final endpoint discharges
it using a constructed oriented auxiliary witness and sign-preserving
extensions. It does not assert pointwise orientation of every parent zero.

`verify_degree.py` checks exact degree six after the positive shift using sparse
integer polynomials. A residual has a nonzero port-independent leading
coefficient, so the squared residuals cannot cancel their highest degree over
the reals. This finite computation is not a Lean degree theorem; no global
minimality is claimed.

Run `python generate.py` followed by `python verify_substitution.py`; the
scripts pin their graph inputs. Candidate SHA-256:
`a90ab59a3ab1b3e9b04c2b962ea79c666a3c2dc90e6941c73f5180ab73c5ee67`.
