# Repository method audit

Repository: https://github.com/lsernau/grh-lean
Pinned revision: 72fead102f663d5c7a407964a13dc0cf9d977207
Inspected: 2026-11-26
Method: source inspection through GitHub connector; no complete rebuild or independent-kernel replay performed here.

## Exact exported scope

`grh/src/Statements.lean` imports only Mathlib and defines four proposition constants.
`grh/src/Main.lean` proves five exported statements:
- `riemannHypothesis : RiemannHypothesis`.
- `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`.
- `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`.
- `LFunction_eq_zero_re : DirichletLZerosOnLine`.
- `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`.

The Dirichlet statements range over N >= 1 and all Dirichlet characters, primitive or not.
Half-plane nonvanishing has Re(s)>1/2 and excludes s=1 for the principal character.
The strip statement has 0<Re(s)<1 and concludes Re(s)=1/2 at a zero.
This is not a statement of GRH for arbitrary automorphic, Artin, or general number-field L-functions.

The README reports only propext, Classical.choice, Quot.sound and successful Lean plus independent-checker runs.
These are repository-reported checks, not reproduced checks in this task.
Toolchain: Lean v4.35.0; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
README estimates 1-2 hours on 12 cores/24 GB, absent Mathlib cache adds about 85 minutes.

## Mathematical architecture

Define
R_{d,q}(x) =
sum_{n<=x,n=1 mod q} Lambda(n)(1-(n/d))(1/n-1/x)
- log(x)/phi(q) - c_{d,q},
where (n/d) is a Legendre symbol, d odd prime coprime to q, and c_{d,q} is chosen so R tends to 0.

The three main geometric inputs are:
A. A normalized, projected Poincare map has short integral lifts and controlled index.
B. Few translates span almost all target forms (second moment / tight-frame method).
C. Integral forms are long (Gram determinant, product formula, and prime-dependent twists).

For dimension D, n>=D/2 independent forms, corrected logarithmic covolume V+2 delta obeys, up to errors,
D*main <= V+2 delta <= n*(main - m*remainder)+error.
The common main quantity cancels. The actual comparison uses main>=0 and n<=D.
The result `star_inequality` is m*totalRemainder <= f*a*(log b)^5.
Then m ~ sqrt(x), log b <= 2*x^epsilon, and a much larger cutoff x1 is controlled by PNT.
It obtains R_{d,q}(x) <= x^{-1/2+epsilon} eventually.

The endpoint is a one-sided Landau criterion applied to the transform
Phi(s)=integral_0^infty R_{d,q}(exp v)*exp((1-s)v) dv.
Its residue at rho != 1 is
(sum_chi ord_rho entireL(chi) - sum_chi ord_rho entireL(chi*(./d)))
 / (phi(q)*rho*(1-rho)).
A quadratic-twist zero-avoidance lemma chooses d so the second multiplicity sum vanishes in the finite rectangle needed for the contradiction.

## Most useful exact modules

- `grh/GUIDE.md`: data, scales, reading order, glossary.
- `grh/src/New/Reduction/MainInequality.lean`: cancellation of short/enough/long bounds.
- `grh/src/New/Reduction/OneSidedBound.lean`: conversion to remainder bound and GRH.
- `grh/src/New/Reduction/Zeros/PrimeError.lean`: exact remainder and transform residues.
- `grh/src/New/Reduction/Zeros/Criterion.lean`: one-sided bound plus zero-free twists.
- `grh/src/Lib/Analytic/Landau.lean`: positivity, abscissa singularity, one-sided pole exclusion.
- `grh/src/New/Reduction/Lattices/TwistedLattice.lean`: prime-dependent twist/product formula.
- `grh/src/New/Spanning/SecondMoment/SpanningTheorem.lean`: translate rank from moments.
- `grh/src/New/UpperBound/ElementaryDivisors/DefectCount.lean`: Frobenius amplification, cone-volume counting.

All URLs can be made stable as
https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/<path>.

## Attribution boundaries

The repository explicitly identifies its Landau lemma as known: Widder II Thm 5b and Montgomery-Vaughan Lemma 15.1.
It identifies character orthogonality/partial summation in PrimeError as known (Davenport).
It classes size-versus-divisibility determinant methods as related to Bost and Laurent; and second moments/tight frames as related to Petersson and Benedetto-Fickus.
Folder and namespace names New/Lib are not claims of novelty.

