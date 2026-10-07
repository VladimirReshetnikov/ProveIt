# Proof audit and integration notes

## Statements established in the article

1. **Total-count normalization:** T(B) <= beta^(2d-1) q^M, including all
   labeled arrangements, repeated vertices, and zero sidelengths.
2. **Top-monomial rigidity:** constancy of the complete cube moment forces
   parity coefficients over every field.
3. **Universal relation:** after eliminating the last cross-section, the
   kernel of eta -> sum eta F(vertex), as a formal polynomial identity,
   is exactly the one-dimensional intended relation space.
4. **Exceptional count:** for H >= 1 and characteristic p > 2H,
   D_H <= (k+1)*((2H+1)^s-(2H+1))/2 * q^(M-1).
5. **Survival:** every respected arrangement survives with probability at
   least a = sum c_j^s. A regular bad arrangement survives with probability
   exactly b = c_0^s. A regular good arrangement has probability exactly a.
6. **Selection:** a first-moment score produces both a positive retained
   mass and a high good proportion in the same outcome.
7. **Explicit parameters:** the stated L, field threshold, Gamma, and
   point-density bound follow with all ceiling and exceptional terms kept.
8. **Extensions:** vector-valued targets, finite abelian targets without
   small torsion, and exact formulas when small torsion is present.
9. **Kernel-class barrier:** a <= R^(-(s-1)) in the stated homogeneous
   nonnegative-Fourier class, with matching powers supplied by Fejer kernels.

## Delicate points checked in the proofs

- Formal polynomial identities are not identified with finite-field
  functions without a zero-count argument.
- Characteristic p > 2H makes the integer coefficient box injective modulo p.
- The intended field-line intersection is exactly the 2H+1 signed integer
  multiples; there are no hidden extra scalars from an extension field.
- Opposite coefficient vectors have identical zero sets, justifying the
  factor 1/2; no independence between zero sets is assumed.
- Repeated physical vertices are selected once, not once per label.
  The actual good survival is at least the labeled moment because all
  probabilities lie in [0,1]. Regularity rules out repetitions for the exact
  bad calculation.
- Extra Fourier terms have nonnegative coefficients. Their omission is used
  only for a lower bound on good arrangements.
- All exceptional bad arrangements are charged before applying the score
  lemma. Their survival is bounded by one; they are not silently discarded.
- Independence between different arrangements is not required.
- The exact theorem retains the stronger good proportion 1/(1+eta).
- Extension-field size does not substitute for the characteristic condition.
- Simultaneous vector-valued selection requires a common good arrangement
  family at the input, not merely separate lower bounds for each map.

## Boundaries of the conclusions

- No new bound for r_l(N), no new density-increment theorem, and no final
  Szemeredi tower reduction is claimed.
- The optimality statement concerns a kernel gain--mass calculation and
  its first-moment certificate. It is not a universal lower bound on the
  best possible subset and does not rule out adaptive or heterogeneous methods.
- The finite checks are supplementary examples and exhaustive small cases,
  not a proof assistant verification of the infinite family of statements.
- The relation-count union bound and s-dependent constants are not claimed
  optimal. The small-field exceptional test is explicitly numerically vacuous.
- No priority claim is made beyond presenting a self-contained proved local
  refinement. No repository-wide or exhaustive literature novelty audit is claimed.

## Recommended next independent review

Check the single-feature universal relation proof, then the bounded-box
intersection with the intended line, then the repeated-vertex survival
inequality. These three points connect the algebraic, Fourier, and
probabilistic parts. Only after this review should the result be propagated
through later sections of Gowers' proof or used as a formalization target.
