# Corrections, safeguards, and novelty scope

No false theorem was identified in the selected source ranges. This is not an audit of the entire repository.

## What should not be re-promoted as new

The preserved centered-Dougall continuation already proves the all-resonance subtraction, the residue polynomial and digamma collapse, and all spectral jets. The canonical section's emphasis on a self-contained first-resonance proof is an integration/dependency distinction. Do not describe this package as newly proving the entire all-resonance continuation.

Classical Rogers–Dougall summation, Gamma recurrence/reflection, ordinary polygamma values, Hurwitz-zeta primitives, and harmonic differentiation all have established antecedents. The explicit sums may also have prior special-case evaluations. The article claims proofs and a scoped extension, not established worldwide priority.

## Principal additions relative to inspected text

1. A necessary-and-sufficient rationality and finite-termination classification for every integral resonance in the positive domain.
2. An exact difference-equation argument upgrading finite formal asymptotics to an identity.
3. Analytic nonrational families whose subtracted remainders sum to zero.
4. A resolvent organization separating every Stieltjes boundary jet from the ordinary higher moments.
5. A half-center Gamma generator for weighted harmonic compositions at all weights, with an explicit signed multiple-polylogarithm sum formula and primitive ladder.

These are not claims that every ingredient or every specialization is historically new. Comparison with the uninspected incoming archives remains outstanding.

## Mathematical guards

- Rationality means membership in the real rational-function field, not necessarily rational coefficients or rational numerical values.
- All classification parameters are positive and satisfy the balancing relation. Symmetric permutations must still respect d0>0.
- A zero total remainder does not imply a rational or terminating summand. The article proves explicit implicit-function families separating those notions.
- A formally finite asymptotic series need not generally be exact without additional reasoning. The rational recurrence and periodicity argument supply that reasoning here.
- Reciprocal-Gamma factors must remain entire germs until after differentiation. The finite-product derivative formula shows the revived tail explicitly.
- The normalized Gamma constants are 1/(2u) at the general center and 1/(4u) in odd-denominator coordinates. The Stieltjes argument is 2u.
- The harmonic theorem concerns C_m, a weighted sum over compositions. It does not evaluate every individual product of harmonic numbers.
- The level-two polylogarithm formula sums over colors. It does not prove individual depth reduction, minimal bases, or period independence.
- The p=1 polylogarithmic endpoint is not assigned a finite value. The ordinary endpoint statements require p>=2; the Gamma closure is for odd p>=3.
- The logarithm in the Gamma primitive is fixed by analytic continuation from v=0. At positive real arguments it is the real logarithm.

## Evidence guards

21,009 exact finite assertions passed. The 28 numerical checks use 40 working digits and a 1e-28 scaled-residual assertion threshold. They are diagnostic, not interval-certified. A tiny residual alone is not a proof. No Lean or other proof-assistant verification is claimed.

During implementation testing, an ordinary Python `1 / integer` in the finite head of the revived rational-sum diagnostic produced machine-precision contamination. It was corrected to `mp.mpf(1) / integer`; all reported results were then rerun with the corrected code. This was an evaluator issue, not a change to the analytic identity.
