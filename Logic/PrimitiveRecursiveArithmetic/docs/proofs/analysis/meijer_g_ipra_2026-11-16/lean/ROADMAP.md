# Formalization roadmap

1. **Exact arithmetic:** signed integers, raw rationals, pairing, bounded lists,
   complex L1 balls, and cross-multiplied inequalities in `Prf PRAAx`.
2. **Hypergeometric core:** term recurrence, partial sums, ratio certificates,
   factorial/geometric tails.
3. **Gamma-ratio products:** guarded multiplication and reciprocal with
   quantitative apartness.
4. **Nonconfluent residues:** Slater right and left evaluators.
5. **Laurent jets:** truncated Laurent convolution, Gamma jets, power-log
   residues, and resonant Bessel cases.
6. **Contour evaluator:** rational polygonal/vertical contours, quadrature,
   pole clearance, closing-side bounds, and finite residue theorem.
7. **ODE and parameter algebra:** kernel polynomial identity, power shift,
   inversion, cancellation, integer block moves, multiplication, derivatives.
8. **Integral transforms:** Mellin, Euler, convolution, the rational-power
   product compiler, Laplace, and certified transform-pair inversion on fixed
   test classes; add the explicit U/1F1-to-G reductions for the Whittaker pair.
9. **Special cases:** exponential, trig, inverse trig, logarithm, incomplete
   gamma, Bessel, Lerch.
10. **Audit:** no placeholders or extra axioms in the trusted path; final
    statements are `Prf PRAAx` derivations; transfer through
    `pra_iff_native` only after ordinary derivations exist.

A recommended early milestone is a complete object-iPRA proof of the cosine,
exponential, logarithm, and rational cases. They require only exact
hypergeometric coefficients and elementary tail bounds, not contour theory.
