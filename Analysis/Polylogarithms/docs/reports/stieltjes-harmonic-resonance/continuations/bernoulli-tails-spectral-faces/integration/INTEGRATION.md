# Proposed ProveIt integration

Baseline: `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

The new continuation should first be retained as a research report, with
its complete proofs and verification records. The section sources can then
be inserted into the corresponding mathematical chapters after the usual
repository review. No source files have been changed by this package.

## Proposed mathematical placements

| Contribution | Source interface | Proposed status |
|---|---|---|
| Universal Bernoulli recurrence and anchored generator | Incoming Quartic Spectral Reconstruction, R4; centered tail moments | Proved for every tail power; repeated even-order extension also proved |
| Fifth- and sixth-power identities | Centered trigamma moments | Eight and eleven specified formal coordinates, with exact nonzero coefficient determinants |
| Cubic all-even-order evaluation | Polygamma-tail identities | Ordinary convergent family; the fourth-order example is `-9*zeta(8)/4` |
| Resonant Laurent coefficients | Quartic report, R5; Stieltjes spectral calculus | Normalization and all local coefficients proved; arithmetic reduction in the resonance index remains open |
| Order-ten completion | Quartic report R1 and Alternating Tails rank refinement | All larger even orders `2b`, `b >= 6`, proved; only new pair relative to both reports is `(10,1924)` |
| Finite decoration closure and marked gaps | harmonic-gaps-mixed-moments, Q4/Q5 | First two-marker case and identical clusters proved; unequal marks resolved only in their fully symmetric sum |
| Explicit spectral face decomposition | Higher Spectral Defects, further questions 3–4 | Ordinary convergent faces and all derivative orders proved |
| Odd-weight rational term and periodic mean-zero cancellation | One-mass spectral/Stieltjes calculus | Complete zero-jet contribution proved; does not remove Stieltjes terms in higher one-mass derivatives |
| Factorial quadratic face identity | Spectral collision calculus | Exact for every face size; not a theorem of functional irreducibility |

## Attribution and overlap

- Minimum-index ordering for products of zeta tails is classical Hoffman
  material. The new all-power assertion is the finite-cutoff Bernoulli
  cancellation and its anchored generator, not that ordering alone.
- The ordinary harmonic-number power theorem is a different family from
  powers of decaying Hurwitz tails.
- The two-factor even-Hurwitz moment cases already exist in the source.
  The repeated-order extension treats arbitrary numbers of equal even-order
  factors. It does not settle the mixed unequal-order higher-product question.
- Bare entire independent-order interpolation is attributed to
  Ihara–Nakamura–Yamamoto. The partition coefficients are classical Hoffman
  symmetric-sum coefficients. The new proof concerns local decorated
  realization, analytic closure, independent marks, and the stated specializations.
- The scalar Dirichlet mixture and a general finite-subtraction compiler
  already exist. The new spectral result supplies explicit face subtractions,
  ordinary integrability, lower-derivative formulas, and the rational zero jet.
- The order-ten congruence and eventual-rank mechanism remain attributed
  to the two incoming reports. This package includes independent exact replay
  of the finite dependencies and a rigorous sufficient threshold.

## Corrections and preserved conventions

No new false theorem was identified in the targeted baseline rank/gap
material. Do not describe the existing lower-index-zero binomial omission
as a newly found erratum: it is already explicit in the source.

Preserve the cutoff `n = 0,...,N-1`, the exceptional low-order endpoint
coefficient, the regular/resonant parity distinction, the exact Stieltjes
sign convention, and the difference between independent derivatives and
diagonal differentiation. Formal coordinate ranks do not prove numerical
period independence. A face contribution need not vanish when merely two
masses coincide.

The audit recommendations in `proof_audits/` were incorporated as described
in `proof_audits/RESOLUTION.md`. They are a record of review of this new
draft, not a list of errors attributed to older reports.

## Claims that must remain open

- The canonical Gaussian S6 and revised S8 period evaluations.
- The unrestricted optimal-prefix conjecture for all unequal even orders,
  and the complete gap-six family.
- General ordered unequal-marker reductions, including all unequal shifts
  induced by unmarked nonpositive deletions.
- Minimal arithmetic or functional depth of the new constants/generators.
- A moment-independent arithmetic span for the growing resonant Laurent
  family, or for every unequal-order higher tail product.
- General finite special-function evaluations of the higher Gamma face integrals.

The historical rejected S8 candidate remains distinct from revised S8.

## Suggested editorial ledger entry

> Bernoulli tails and spectral faces: retain the all-power and repeated
> even-order Bernoulli cancellation, anchored generators, explicit fifth/sixth
> ordinary sums, complete local resonant Laurent formulas, the exact order-ten
> missing-index certificate with full dependency replay, several-marker
> decorated Gamma–Stieltjes identities, and ordinary all-order simplex-face
> formulas with rational zero-jet and periodic corrections. The first two-marker
> target and the order-ten family are proved in their precise stated scopes.
> Keep formal rank separate from arithmetic independence. Unequal-marker
> antisymmetric channels, general higher unequal-tail products, and Gaussian
> S6/revised S8 remain open.

## Verification and implementation notes

The finite algebra helper in `verification/moment/p10_dependency_algebra.py`
is an attributed adaptation of the source contraction algebra. Its certificate
is regenerated and checked by `verify_p10_dependencies.py`. The independent
Faulhaber route in `verification/allpowers/verify_allpowers.py` does not use
the new generator to construct the comparison moments. The numerical
quadrature scripts are explicitly diagnostic and do not certify interval bounds.

All equation labels are namespaced (`tp:`, `et:`, `mt10:`, `gm:`, `sd:`).
The notation is reset locally in the article; retain those resets if sections
are moved separately. The standalone source and modular source must be
regenerated together using `build.py` after edits.
