# Proposed formalization dependency plan

This file is a plan, not executable Lean code and not a claim of formal
verification.

## Finite algebra first

1. Define uniform finite cubes, real multilinear Fourier coefficients, and
   cell degree for finite observations.
2. Prove closure of cell degree under readout, independent products, and
   sums of functions on at most m input blocks (Lemma 2.2).
3. Formalize the pointwise reporting identity before any probability
   argument. Endpoint choices should be explicit in the definition.
4. Formalize the exact singleton-binomial moment identities and the 20-bit
   witness. Rational arithmetic and finite sums suffice.
5. Verify the tensor Fourier transform identity and its equivalence to
   the full cube transform for block-symmetric functions.

## Probability interface

6. Establish the score/tower identities and the conditional-expectation
   projection inequality used by the reporting gate.
7. Prove the fourth moment of an independent centered sum and the
   conditional Jensen bound.
8. Formalize the fixed-batch induction assuming an abstract transfer lemma.
   This separates the finite recursion from the analytic normal approximation.

## Analytic closure

9. Supply the normal Stein solution derivative estimate, or import an
   appropriately established theorem with exactly matching hypotheses.
10. Prove the Wasserstein averaging estimate and the hyperplane-boundary
    transfer lemma. The latter needs a coupling realization, moment
    interpolation, normal density bounds, and careful endpoint handling.
11. Formalize truncated-normal mean differentiation, symmetric pairing,
    the Gaussian deficit identity, and the explicit uniform inequalities.
12. Discharge the symbolic integer/exponent inequalities without expanding
    the batch size into an enormous numeral.

## Final assembly

13. Prove one-bit oddization and singleton-sum preservation.
14. Assemble Theorem 1.1 and the all-degree-budget corollaries.
15. Keep the qualitative composition consequence in a separate theorem
    so the novelty/dependency boundary remains explicit.

A useful first independently checked milestone would be Theorem 7.2 plus
Lemma 3.1's pointwise degree statement. Neither requires the full analytic
normal-transfer library.
