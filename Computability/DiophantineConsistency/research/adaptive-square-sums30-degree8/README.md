# The 30-variable degree-eight equation

The [base-10 equation](../../equation8-30.pdf) has 30 separately named positive
integer unknowns and a 138-operation circuit. The no-premise Lean theorem
[`IPRAAQ30Native.literal_equivalence`](../../Lean/DiophantineConsistency/IPRAAQ30Native.lean)
asserts a derivation in the project's native intuitionistic PRA candidate: the
fixed-port equation has no positive zero if and only if Foundation's particular
mapped ZFC refutation predicate is negated. Its [focused paired replay](../../research/adaptive-aq30-proof/NATIVE.md)
matched eleven modules and all nine rebuilt model objects. This is a historical
fixed-snapshot result with inherited project, package-transitive and dynamic
ancestry; a fully authenticated current-source closure remains open.

The graph eliminates the positive named W coordinate from the pinned
31-variable equation by substituting its defining expression
`Bt = C*(X + K*q) - F*q`. It has 21 squared residuals. The finite
`verify_substitution.py` checks that all 22 parent residuals agree after this
substitution, with the removed residual identically zero. The identity alone
does not show that the reconstructed W is positive.

The [model proof](../../research/adaptive-aq30-proof/README.md) derives that
positivity from the actual first norm and root equation, using the positive and
negative components of `splitEval Bt`; it does not assume a signed intermediate
is naturally nonnegative. Lean proves the shifted no-zero statements equivalent
for every natural port vector in every IΣ₁ model, and the native endpoint uses
the exact fixed ports.

`verify_degree.py` checks exact degree eight after the positive shift using
sparse integer polynomials. A maximum-degree residual has a nonzero
port-independent leading coefficient, so the squared residuals cannot cancel
their highest degree over the reals. This finite computation is not a Lean
degree theorem; no global minimality is claimed.

Run `python generate.py` and then `python verify_substitution.py`; the scripts
pin their graph inputs. Candidate SHA-256:
`f6c88de69011dc070c3cb642cf12bc27bb20c6ee92eaabb56dc1ccd884f685ad`.
