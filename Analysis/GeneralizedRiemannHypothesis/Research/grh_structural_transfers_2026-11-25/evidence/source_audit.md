# Targeted source audit: 25 November 2026 (Pacific date)

## Provenance and verification scope

Repository: https://github.com/lsernau/grh-lean

Inspected commit: `72fead102f663d5c7a407964a13dc0cf9d977207` (confirmed by local `git rev-parse HEAD`). This was the head returned by the GitHub connector. No source file was modified. The static scan summarized in `static_audit.json` strips nested Lean block comments, line comments, and strings, then searches active source tokens. In `grh/src` it covered 803 Lean files and 477,124 physical lines; in `grh-compact/src`, 794 files and 112,827 lines. It found no active `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, or `native_decide` tokens in either source tree.

That is **not** a successful build, axiom audit of compiled constants, semantic audit of every definition, or independent kernel replay. `lean` and `lake` were unavailable on PATH in this environment. The repository's readable README reports successful Lean builds, use only of `propext`, `Classical.choice`, `Quot.sound`, acceptance of exported dependencies by nanoda/con-leche/con-ron, and a Comparator check. Those are published checks rather than locally repeated checks. The final report also consulted Andrew Sutherland's independent verification page for the same commit and matched all 1,625 source-file hashes to its published manifest. The repository's separate `Challenge.lean` intentionally has `sorry`; it lies outside `src`, is not imported, and is not part of the ordinary build. Do not describe the lexical result as no `sorry` anywhere in the repository.

## Exact theorem scope

`grh/src/Statements.lean` imports only Mathlib and defines `DirichletLNonvanishingRightOfHalf` for `(N : Nat) [NeZero N]`, `chi : DirichletCharacter Complex N`, and `s : Complex`, with real part above 1/2 and the principal-character pole removed. The final five declarations in `grh/src/Main.lean` prove this, RH, and equivalent zero-line formulations. All moduli and imprimitive characters are included. There is no quantified number field, Artin representation, or general cuspidal automorphic L-function in these final statements.

Consequently, use **Dirichlet GRH** consistently. The development's use of Hecke L-values on CM fields inside the proof does not establish GRH for all those Hecke L-functions. An integral critical-value identity and an arbitrary-complex-variable zero statement are different theorems.

## Transfer interfaces and precise caveats

All paths below are relative to `grh/src`.

| Interface | Exact declarations | Meaning and required transfer work |
|---|---|---|
| Common lattice | `New/Reduction/Lattices/TwistedLattice.lean`: `TwistedLattice`, `integralVectors`, `IndexLe`, `CovolumeLe`, `covolume_add_index_nonneg` | Lifts depend on a twist; the underlying family of vectors does not. At each finite place an integral carrying matrix must work for **all** twists allowed at that place. Covolume concerns the untwisted lift, including every conjugate. Rational Gram coordinates are built into the interface. Independently favorable local objects cannot be multiplied without a common global comparison and height bound. |
| Short forms and coverage | `New/Reduction/ShortAndEnough.lean`: `span_short_integralRamified_eq_top`, `indexLe_normalizedPoincare`, `enough_forms` | Short integral source forms span; a controlled number of translates fill at least `(1-4/b^2)` of target dimension. A new target must retain this almost-full coverage and control the missing complement. |
| Lower covolume | `New/Determinant/Twist/LongForms.lean`: `integral_forms_long` | Independent target forms of size at least `(1-4/b^2)d`, index bound delta, covolume bound c satisfy `d(mainAmount-3 f a log(b)^4) <= c+2 delta`. The proof completes to a basis with auxiliary forms and uses a local twist for every prime and embedding plus globally bounded determinant ratios. |
| Master comparison | `New/Reduction/MainInequality.lean`: `star_inequality` | `m totalRemainder <= f a log(b)^5`. The main amount cancels exactly between short-form upper and long-form lower bounds. A proposed new arithmetic statistic must arise on both sides with a compatible normalization, not merely be substituted into this final inequality. |
| Prime statistic | `New/Reduction/Zeros/PrimeError.lean`: `lambdaKResidueClass`, `primeRemainder`, `isPolar_primeRemainder` | Coefficients are specifically `Lambda(n)(1-chi_K(n))` for `n = 1 mod q`. These are abelian congruence and quadratic splitting data. A nonabelian Frobenius coefficient requires a new local divisibility mechanism and matching period constant. |
| One-sided zero exclusion | `New/Reduction/Zeros/Criterion.lean`: `LFunction_ne_zero_of_primeRemainder_le` | For all auxiliary primes d in a suitable progression, eventual upper bound `R_q(x) <= x^(beta-1)` excludes zeros to the right of beta. The proof chooses d so all finitely many relevant quadratic twists are zero-free in a rectangle; this avoids cancellation of target zero residues. A generalized zero criterion must supply an analogous no-cancellation input. |
| Actual bound | `New/Reduction/OneSidedBound.lean`: `Data.primeRemainder_le`, `eventually_primeRemainder_natCast_le`, `grh` | `R_q(x) <= phi(q) log(b)^6/m + |R_q(x1)| + log(b)|R_1(x1)|`, followed by `m >= sqrt(x)`, log b subpower of x, and a much larger x1. Fixed-modulus qualitative eventual bounds; no ready-made uniform conductor-aspect constants. |
| Uniform torsion specialization | `New/Congruences/Selmer/RootsOfUnity.lean`: `exists_rootsOfUnity_ellVal_eval_le_add` | Given number of variables, radius rho, total valuation budget beta and epsilon, first chooses a bound h0; then every finite family of integral polynomials with witnesses fits a common tuple of roots of orders dividing ell^h0, preserving each witness valuation within epsilon. It is degree-free, but it does not require maximal order. |
| General twist | `New/Congruences/Selmer/GeneralTheorem.lean`: `exists_anticyclotomic_twist`, `IsSmallTwist` | Works simultaneously for finite families of **SelmerDatum** and **StickelbergerSystem**, and first m powers. Character is anticyclotomic, ell-power order, trivial on decomposition groups above ell, ramified at each new auxiliary prime. The conclusion is normalized Selmer length at most beta+epsilon, not automatic zero, and not an estimate for the untwisted original Selmer group. |
| Selmer input | `New/Congruences/Selmer/SelmerData.lean`: `SelmerDatum` (105–151), `congruenceTerm` (77) | Requires residual absolute irreducibility in Burnside form, finite global and local length terms, constrained dimensions of permitted local cocycles, and scalar inertia gamma away from ell with zeta^2-1 a unit. These are mathematical restrictions, not bookkeeping. |
| Congruence bound | `New/Congruences/Selmer/SelmerData.lean`: `congruenceTerm_le` (692); `MainSummands.lean`: `normLength_congruenceTerm_le` (155), `eventually_exists_selmerDatum` (294) | A scalar difference between a representation and its conjugate Tate dual annihilates the Hom module. The source ensures this difference is nonzero via a positive cyclotomic weight shift and selected Frobenius. It need not survive a central self-dual replacement. |
| Projections and special values | `New/OneLift/LiftVolumeHeight.lean`; `New/Congruences/FirstOrder/DenominatorBound.lean`: `denominatorLe_clearingBound`; `New/Congruences/FitTwistsExist.lean`: `exists_isRegularFamily` | The projection is to a space of theta lifts, with explicit orthogonality to false lifts and a congruence denominator. A new individual automorphic form cannot simply be picked out without its projector-denominator and local-type analysis. |

## Extra obstruction, fully proved in the attached fragment

`sections/inertia.tex` proves a rank/determinant obstruction and a stronger symmetric-power obstruction. If a representation's determinant is trivial on inertia away from ell and the prime-to-ell part of its rank is 1 or 2, it cannot provide the required scalar inertia element. Every positive symmetric power of a rank-two representation with determinant unramified away from ell fails the same test, for every ell and every Tate twist. This includes nonsemisimple and wild-inertia matrices; no reduction-type case split is necessary.

For central odd symmetric powers of an elliptic-curve Tate module, there is also a global obstruction: the rational representation is isomorphic to its conjugate Tate dual. An anticyclotomic preliminary twist can change scalar inertia but preserves that global self-duality. Root's other agent is developing the global Hom-length proof and a quotient/regularization analysis.

## Source normalization that avoids the global obstruction

`MainSummands.lean` (56–76) uses `rho^c ~= rho^vee * chi^(-(t-1)_Nat)`, with natural-number truncated subtraction. Hence the conjugate Tate dual has a **strictly positive** cyclotomic shift `(t-1)_Nat+1` relative to rho, including when t=0. The annihilator in the proof at lines 160–174 is alpha times `1-p^(rank*((t-1)_Nat+1))`. Thus no mistaken t=0 argument may assert the source treats weight-one self-dual representations. It does not.

## Primary sources for elliptic-curve specialization

Milne, *Abelian Varieties*, author's course notes, section 13 (Weil pairings): https://www.jmilne.org/math/CourseNotes/AVc.pdf . Web reference returned: `turn963362809search6` (root must open it before final web citation). Nondegenerate equivariant pairing on torsion induces determinant cyclotomic and Tate self-duality. The linear-algebra statements in the new fragment are proved directly, so no novelty claim rests on a literature citation.

Andrew Snowden, Math 679 lecture 2, *Elliptic curves*, author's 2013 lecture notes: https://websites.umich.edu/asnowden/teaching/2013/679/L02.html . Web reference `turn963362809view0`; the Tate-module section explicitly concludes determinant equals cyclotomic from the Weil pairing.

## Assessment

The reusable part is strong enough to justify further targeted research. The new consequences above are **obstruction and interface theorems**, not resolutions of BSD, symmetric-power GRH, or Bloch–Kato. Nonabelian prime detectors require arithmetic realization; individual-form transfers require projector control; central self-dual Selmer targets additionally require a revised theorem accommodating a free conjugate-dual Hom component. These are distinct gaps and should not be hidden in an omnibus 'standard inputs' hypothesis.
