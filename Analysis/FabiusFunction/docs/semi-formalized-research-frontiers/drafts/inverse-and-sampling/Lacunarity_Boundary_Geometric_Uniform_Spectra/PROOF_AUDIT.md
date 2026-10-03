# Proof audit

## Claim-level dependencies

| Result | Essential steps | Status |
|---|---|---|
| Geometric energy identity | Ratio-implied tail domination; infinite summation by parts with vanishing boundary term | Proved in Lemma 2.1 |
| Sharp head inequality | Apply the energy inequality to the normalized tail; solve a quadratic; exhibit the equality family | Proved in Lemma 2.2 |
| Squared-coordinate certificate | Nonnegative geometric-envelope slacks, with a lower geometric bound on their tails | Proved in Lemma 2.3 |
| Two-moment rigidity | Independent-uniform moment expansion and the squared-coordinate certificate | Proved in Theorem 3.2 |
| Maximal support singleton | Apply the same inequality to normalized coefficients, rather than coefficient squares | Proved in Theorem 3.4 |
| Smooth sharpness | Delete one dyadic factor, restore variance, calculate every derivative norm by disjoint support translates | Proved in Lemma 4.1 and Proposition 4.3 |
| Sharp inverse exponent | Fourth-moment upper bound; TV upper bound for explicit smooth witnesses; geometric scale interpolation | Proved in Theorem 4.5 |
| Hellinger order | Fixed five-uniform convolution; centered Taylor cancellation; explicit endpoint strips; dilation of square-root densities | Proved in Lemmas 5.1–5.2 and Theorem 5.3 |
| Quartic testing order | Bounded fourth-moment test; product Hellinger affinity; explicit alternatives | Proved in Theorem 6.1 |
| Sharp prefix constants | A continuous whole-tail contraction preserves variance and the smooth class | Proved in Theorem 7.1 |
| Relative-ratio extension | Monotone p_j/w_j; weighted energy identity; tail contractions and common smoothing | Proved in Theorems 8.1–8.2 |

The theorem numbers refer to the packaged PDF/source.

## Delicate points handled explicitly

1. TV is `sup_B |P(B)-Q(B)|`, hence half the L1 density distance. A fourth
   moment on [-1,1] changes by at most TV, not a silently different convention.
2. The critical ratio equals the reference's own ratio. A geometric reference
   of ratio rho > 1/2 is not the dyadic reference with slack rho > 1/2.
3. The core proof controls the head excess and every squared coefficient.
   A generic L2-to-square-root argument would lose an unnecessary exponent.
4. The lower witnesses retain infinitely many positive uniform factors.
   All derivative inequalities defining the predecessor's smooth class are
   proved, not extrapolated from tested derivative orders.
5. Hellinger smoothing separates the support boundary from the interior.
   The proof never divides by a zero density outside its support and does
   not assume finite chi-square distance across unequal supports.
6. The statistical lower bound uses H^2 = O(h^4). TV = O(h^2) alone would
   not prove the claimed quartic testing lower bound.
7. The prefix lower bound varies a continuous tail-contraction parameter
   at each fixed r, so it is genuinely local as law distance tends to zero.
8. A positive lower ratio bound in the nongeometric extension is used to
   interpolate discrete witness scales. Without it, only a subsequence
   obstruction to a better exponent is claimed.
9. Fixed maximal support plus variance is rigid only in the exact critical
   cone. The supercritical exact-support problem remains open here.

## Independent checks performed

The recorded Python run passed 29,776 exact assertions, with deterministic
seed 20260930. These include finite padded-sequence evaluations of the
infinite-tail energy identity, sharp head bounds, squared-coordinate and
radical bounds, deleted-factor moment and support identities, smooth-class
inequalities for orders 0 through 100, continuous-tail estimates, and finite
relative-ratio profile identities.

The PDF was compiled with pdfLaTeX through latexmk, rendered to page images,
and visually inspected. Final compilation checks include the absence of
undefined cross-references/citations, overfull boxes, and TeX errors.

## Limits of the verification

- No Lean, Rocq, or other proof-assistant checking was performed.
- No independent peer review has occurred.
- Finite assertions are regression tests, not proofs for all parameters.
- No TV or Hellinger distances were estimated by numerical integration.
- The explicit rate exponents are sharp; leading constants are not optimized.
- The literature check was targeted, not exhaustive.
- The claims concern anchored recovery and testing, not global two-point
  minimax estimation over arbitrary nearby spectra.
