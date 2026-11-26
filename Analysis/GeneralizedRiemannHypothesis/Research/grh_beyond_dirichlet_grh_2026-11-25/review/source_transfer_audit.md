# Source-level transfer audit

Repository: `lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
Inspection: readable edition `grh/`, via local source checkout. This is a source and mathematical-interface analysis, not a fresh Lean build or an independent kernel audit.

## 1. What the architecture actually compares

`grh/src/New/Reduction/MainInequality.lean`, `New.star_inequality`, imports `New.Determinant.Twist.LongForms` and `New.Reduction.ShortAndEnough`. With target dimension d, n independent images, main amount M, m-fold prime remainder R, logarithmic squared covolume c and index bound δ, the mechanism is:

* Short forms and Hadamard give c ≤ n(M − mR + L), L = f a log^4 b.
* Enough forms give (1−4/b²)d ≤ n ≤ d and a set t of translates with |t| dim(source) ≤ 5d log(1+2b²).
* The index is at most d I, I=10 log(1+2b²) errorUnit, errorUnit=f a log³ b.
* Long forms give d(M−3L) ≤ c+2δ.
* Since M+L≥0 and n≤d, cancellation gives n mR ≤ d(4L+2I). Since n≥d/2, mR≤2(4L+2I)≤f a log⁵b.

This is not a generic theorem that automatically imports to every L-function: identifying M and R on both sides, with their exact cancellation, is the main arithmetic construction.

## 2. Short/enough/long interfaces

### Theorem A, short and small index

`New.Data.span_short_integralRamified_eq_top`, `ShortAndEnough.lean:254`, spans the ramified source by vectors integral at every p-adic place whose images under every finite-group translate of normalized Poincaré and untwisted theta chain have all-conjugate squared norms ≤exp(M−mR+L).

`New.Data.indexLe_normalizedPoincare`, same file:373, bounds the index of any finite family selected from finitely many translates by

`#t * finrank ℂ D.ramifiedSourceForms * (2 * D.errorUnit)`.

The normalization `D.invGainFactor` is rational, a product of prime powers with exponents minus floor(gain−divisibilityError). This cancels the local divisibility gains against the archimedean normalization. The index certificate is uniform across every allowed twist at a given p-adic place; this uniformity is required later.

### Theorem B, enough forms

`New.Data.enough_forms`, same file:448, gives positive target dimension, a finite translate set t satisfying the above cost bound, and rank at least `(1−4/b²)*d`. The source is `Spanning/SecondMoment/SpanningTheorem.lean`, especially `isNearIsometry_e₀_comp_scaledPoincare`, `sum_hilbertSchmidtNorm_scaledPoincare_sq_le`, and `isSpread_goodPoincare`.

It is second-moment coverage, not a sharp estimate for each individual eigenform. The target is a high-rank family selected by finite-group idempotents; replacing it by a prescribed low-rank automorphic representation loses the proved hypotheses.

### Theorem C, long forms

`New.Data.integral_forms_long`, `Determinant/Twist/LongForms.lean:231`, applies to independent y₁,…,yₙ with n≥(1−4/b²)d, index δ and covolume c. Its conclusion is d(M−3fa log⁴b)≤c+2δ.

The proof extends the n vectors to a basis using auxiliary forms, chooses a different admissible twist for each p-adic place, and uses a generic twisted-lattice product-formula inequality. Completing the basis costs at most d b because the deficit is ≤4d/b² and each extra vector has cost about 2x₁²b²; the separation b≫x₁² absorbs it. This small deficit is crucial: a fixed fraction of missing directions would cost far too much with these auxiliary forms.

## 3. Genuinely generic twisted-lattice theorem

`grh/src/New/Reduction/Lattices/TwistedLattice.lean` defines `New.TwistedLattice V T` for a complex vector space V and arbitrary index type T with basepoint 1. It includes linear maps Θξ to inner-product spaces, integral lattices at every p-adic identification, an `IsAllowed p ξ` predicate, a pairing-integrality condition using conjugate identifications, and rational positive-definite Gram coordinates for the base twist.

`integralVectors ι` is the intersection of inverse images of all allowed-twist lattices. `IndexLe y δ` supplies a p-adic integral matrix carrying y into this intersection with bounded determinant loss, uniformly over the twists. `CovolumeLe y c` bounds all conjugates of the base-twist Gram determinant. `volume ξ=det(Θξ*Θξ)` when the relevant spaces are finite dimensional.

`New.TwistedLattice.covolume_add_index_nonneg` at line477 is generic. Hypotheses:

1. All Θξ injective.
2. y₁,…,yₙ,z₁,…,zₙ′ form a basis (d=n+n′).
3. An independently selected allowed twist ξι at every p-adic identification ι.
4. y has covolume c and index δ.
5. γ(ξ)≠0 and γ(ξ)Θξzᵢ integral at every allowed place.
6. All conjugates of Θ₁zᵢ have squared norm ≤exp(b_short).
7. Families |γ(ξι)|⁻² and Z(1)/Z(ξι) have heights ≤b_denom and ≤b_volume.

Conclusion:

`0 ≤ c + 2δ + n′(b_short+b_denom) + b_volume`.

The factor 2 on δ comes from the two Gram factors, one at ι and one at its conjugate. The local choices need not be induced by a single global twist. This is the portable mechanism, with all quantitative losses exposed.

## 4. Determinant and Selmer interfaces

`New.OneLift.LiftVolumeHeight.lean` defines comparison operators Uξ from integral tight frames. For each single theta lift uξ, compression to its range gives

`det(uξ* uξ) * det(pr Uξ) = C * (Hξ/H1)^d`,

where Hξ is a product of partial Hecke L-values and C≠0 is independent of ξ. The key generic identity is `New.Data.normDet_sq_mul_det_compression` (line51); the arithmetic theorem is `heightLe_liftDeterminant_ratio` (line729).

Archimedean bounds on `det(pr U1)` and p-adic denominator bounds on `det(pr Uξι)` bound the height of determinant ratios. Summing over m lifts and using chain norm factorizations yields the negative main amount in `heightLe_chainDeterminant_one_div`.

`New.Data.IsRegularFamily`, `Determinant/Twist/FitTwists.lean`, requires:

* the chosen conductor norm prime to the corresponding p;
* small heights for inverse L-value ratios for each of the first m powers, both signs, and all ramified critical pairs;
* projection-denominator bounds summing over p within `denominatorBudget=fa log³b/(mk)`.

`New.exists_isRegularFamily`, `Congruences/FitTwistsExist.lean:517`, constructs this using `exists_mFoldTwist_hasDenominatorsLe` and `exists_mFoldTwist_hasDivisibleSelmerLengthLe`. The Selmer-to-denominator mechanism is `FirstOrder/DenominatorBound.lean:1321`, `denominatorLe_clearingBound`.

The concrete arithmetic representation hypotheses are much stronger than merely being a Galois representation. `IsMainSummandLike` in `GaloisRepresentations/SelmerHypotheses.lean:434` includes conjugate self-duality, carefully constrained weights and local conditions, bounded inertia losses at selected primes, matrix-span irreducibility over integral lattices, prescribed scalar elements, and scalar inertia of sufficiently large residual order. These hypotheses must be re-proved for a new family.

## 5. General simultaneous twisting

`New.Selmer.exists_anticyclotomic_twist`, `Congruences/Selmer/GeneralTheorem.lean:392`, is more generic than the final application. It takes a CM field E, finitely many `SelmerDatum` objects and `StickelbergerSystem` objects, a prime p, common auxiliary local data, and a sufficiently large torsion level. It produces a finite auxiliary prime set Q and an anticyclotomic character ψ of p-power order such that every ψ^j, 1≤j≤m, has:

* Selmer length at most the datum's baseline βT+ε;
* Stickelberger evaluation valuation at most βY+ε;
* small sum of tame inertia losses;
* conductor disjoint from prescribed bad places, with nontrivial ramification at every place in Q.

The theorem contains **no bound on the norms of the auxiliary primes or on the conductor norm**. A bound on the p-power order of a character does not bound the norms of primes at which it ramifies. Therefore it does not give a density theorem, least-twist theorem, fixed-conductor theorem, or conductor-aspect subconvex estimate.

`SelmerDatum` (`SelmerData.lean:105`) itself requires residual irreducibility in Burnside form, a local-condition dimension inequality, finite global and local loss terms, and scalar inertia with ζ²−1 a unit. `StickelbergerSystem` (`StickelbergerSystems.lean:222`) requires a nonzero untwisted starting value and precise Euler-factor norm relations. The theorem is not unconditional nonvanishing for arbitrary arithmetic families whose reference L-values may vanish.

Lengths are normalized so that length(O/p)=1, while coefficient rings may have arbitrarily large ramification. A positive normalized length may be below1; a bound β+ε<1 does not itself imply the integral Selmer module vanishes. Finite length can exclude a free/divisible rank in the specified module, but interpretation as a classical arithmetic rank needs its own comparison theorem.

## 6. Degree-free torsion specialization and the extension

The best compact export is `RootsOfUnity.lean:474`, `exists_rootsOfUnity_ellVal_eval_le_add`, together with the powers version `GeneralTheorem.lean:325`, `exists_rootsOfUnity_ellVal_eval_le`.

For fixed p,s₀,m,r, finite valuation budgets βᵢ, and ε>0, the order bound H is chosen before the integral polynomials and reference points. It produces one tuple of p-power roots ζ with v(ζa−1)≤r/m and v(Pᵢ(ζ^j−1))≤v(Pᵢ(xᵢ))+ε for every i and 1≤j≤m, assuming all v(xᵢa)≥r.

A sufficient bound follows from the harmonic criterion with B=∑βᵢ, δ=min(ε,1)/(s₀+2), h*=min{h≥1:1/φ(p^h)≤r/m}:

`mB+1 < δ ∑_{h=h*}^H 1/(h+1)`.

My standalone TEX contribution `torsion_series_fitting.tex` proves the same-H extension to integral formal series over completed Cp and a simultaneous Fitting-minor profile corollary. The proof combines uniform total-degree truncation on the bounded torsion grid with approximation of finitely many coefficients and reference points by algebraic elements. It handles ζa^j=1 explicitly: zero coordinates have infinite valuation and only improve convergence.

For finitely many matrix-size pairs, selecting one witness minor attaining the least minor valuation at its reference point yields a common torsion tuple preserving all these minima up to ε. This controls cumulative invariant-factor valuations, not individual ones. Rank-only preservation needs only one maximal nonzero minor per matrix, and benefits from the stronger linear-depth nonvanishing lemma proposed by the root agent and independently checked here.

## 7. Boundaries of plausible applications

* **P-adic families / Fitting ideals:** concrete theorem above is available once integral matrix presentations and finite reference valuations exist. Arithmetic construction and identification are separate.
* **Simultaneous arithmetic nonvanishing:** general twisting is plausible infrastructure, but must supply actual Stickelberger systems, nonzero reference values, and prescribed Euler relations. It does not magically show all critical values nonzero.
* **Congruences and Selmer estimates for new lifts:** plausible but requires all local types, irreducibility, integral lattice and scalar inertia clauses. No generic Bloch–Kato conclusion follows.
* **Other L-functions / number-field GRH:** the prime-error criterion and geometric cancellation would have to be reconstructed. The current data is tied to Dirichlet characters over Q, special CM extensions, and a two-scale weighted prime sum.
* **Lindelöf/subconvexity/Ramanujan/simplicity:** neither determinant control nor zero-free regions supply the required individual quantities. An operator with eigenvalues T and T⁻¹ has fixed determinant and unbounded largest eigenvalue. The mechanism averages across a large space and has no eigenvalue isolation. A zero-free-half-plane result has no lower bound on derivatives at critical-line zeros, hence no simplicity statement.

## 8. Dependency evidence

The accompanying `source_dependency_summary.json` traverses literal imports within `grh/src` and counts repository modules, including the queried module itself but excluding external Mathlib internals. No listed interface imports `Main`, `New.Main`, or `New.Reduction.OneSidedBound` transitively.

* TwistedLattice:109 repository modules; no `New.Reduction.Zeros.*` module.
* RootsOfUnity:103; no zero module.
* GeneralTheorem:208; no zero module.
* FitTwistsExist:723; imports `Zeros.PrimeError` only, not the zero-free criterion or GRH conclusion.
* LiftVolumeHeight:664; same prime-error definition dependency.
* ShortAndEnough:562.
* LongForms:754.
* MainInequality:791.

These are static import results, not independent Lean proof verification. They support describing the portable lemmas as ingredients of the proof rather than deductions from its RH/GRH exports.

## 9. Source classification and novelty caution

`INDEX.md` explicitly classifies `Lib` as results believed known and `New` as proof setup/steps plus known results specialized to that setup; neither directory nor namespace is a novelty declaration. `REFERENCES.md` says only a subset of citations was compared with the original sources. Related-work paragraphs list Bost/Laurent for determinant size-versus-divisibility, Hida/Prasanna for congruence denominators, Mazur–Rubin and Kriz–Nordentoft for twisting, and Kriz–Nordentoft/Serban/Kurihara for degree-free torsion specialization. New presentation or extraction is not evidence of literature novelty. The formal-series/Fitting extension and sharper nonvanishing bound are rigorous deductions developed in this analysis; priority would require a separate comprehensive literature comparison.
