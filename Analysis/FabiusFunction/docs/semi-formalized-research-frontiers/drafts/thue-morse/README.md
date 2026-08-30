# Thue-Morse

The Thue-Morse side of the corpus, consolidated (2026-08-28) into the
single volume [`Thue_Morse_Atlas_and_Frontiers.tex`](Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.tex)
([PDF](Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.pdf),
133 pp):

- **Part I** — *A Unified Formula Atlas for the Thue–Morse Sequence*
  (formerly `Thue_Morse_Formula_Atlas/`);
- **Part II** — *A Finite-Block Calculus for the
  Fabius–Rvachev–Thue–Morse System* (block bridges, the zeta–Lambert
  tail calculus, q-Richardson weights; formerly
  `Fabius_Rvachev_Thue_Morse_Frontier_Results/`, its figures and
  reproducibility bundle under `assets/`).

Both parts carry extensive inline Lean crosswalks. As of 2026-08-28,
`ThueMorseComplexProductBridge.lean` supplies the finite-product core in total
complex form at every level: the sinc and negative-Laplace block equalities
include the removable origin, with quotient normalizations away from zero and
simp laws for the normalized origin values, together with the exact finite
Fourier--Laplace rotation between the two prefixes. The analytic-logarithm,
certified-remainder, and measure-refinement results named in the volume also
have formal counterparts; the remaining roadmap obligations stay explicitly
labeled.

The current reciprocal-Gamma jet/tower overlay preserves that historical
status and pins the first tranche to `0ba35abd4`.  The exhaustive five-theorem
API of `ReciprocalGammaJets.lean` is `deriv_Gamma_inv_neg_nat`,
`hasDerivAt_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_zero`,
`analyticOrderAt_Gamma_inv_neg_nat`, and `tendsto_Gamma_inv_div_add_nat`.
It gives the exact first jet `(-1)^r r!`, simple analytic order, and punctured
local coefficient of the entire reciprocal Gamma function at every `-r`; it
does not assign a derivative to raw Gamma at a pole.

At the same commit, the first eight public declarations of
`ThueMorseGammaTower.lean` are
`hasDerivAt_dirichletMellinContinuation_neg_nat`,
`deriv_dirichletMellinContinuation_neg_nat`, `thueMorseGammaLog`,
`thueMorseGammaTower`, `thueMorseGammaLog_eq_mellin`,
`thueMorseGammaLog_eq_integral`, `thueMorseGammaLog_dyadic`, and
`thueMorseGammaTower_dyadic`.  The current integrated tree adds the ninth,
`ofReal_exp_mpLimit_eq_gammaTower_div`.  The two definitions are total for real
`a`; the Mellin, integral, dyadic, and ratio theorems require positive
parameters.  GammaLog is the chosen derivative coordinate, not a proved
`Complex.log` identity.  Only the parameter-`a` differential and iterated
differential ladder remains open in this tower tranche.

`CentralBinomialValuation.lean` supplies the atlas's direct central-binomial
crosswalk.  Its exhaustive public API is
`padicValNat_two_centralBinom`,
`thueMorseSign_eq_neg_one_pow_centralBinom`, and
`padicValNat_two_centralBinom_eq_zero_iff`: the valuation of `C(2n,n)` is
`binaryWeight n`, its parity gives the Thue--Morse sign, and it vanishes only
at `n = 0` (positive powers of two have valuation one).

`BinaryDigitFloor.lean` supplies the exact floor-difference form of a binary
digit.  Its exhaustive public API is `div_two_pow_succ_eq_div_div`,
`sub_two_mul_div_two`, `div_two_pow_sub_two_mul_div_two_pow_succ`, and
`testBit_toNat_eq_div_sub_two_mul_div`: dyadic quotients compose, parity is the
remainder after twice the quotient, and the `j`-th bit indicator is the
difference of two consecutive dyadic quotients.  These are total identities on
natural-number inputs; they do not assert a real-floor or analytic extension.

The member drafts were absorbed content-preservingly (labels, citation
keys, and asset paths mechanically prefixed per part; wrapper metadata
and section-counter handling normalized; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

The consolidated volume directory is the only document build root.  The
relocated Part II bundle under `assets/` contains figures and
reproducibility material only; it no longer contains a standalone TeX or
PDF manuscript.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
