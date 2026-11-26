# New results: exact interfaces and formalization status

## Verification status

The new results in the accompanying paper have complete human-readable proofs
and received independent mathematical review during this analysis. **They have
not been formalized in Lean and have not been checked by Lean's kernel.**
No `.lean` file in this package purports to prove them.

The source extraction at `../upstream/project/` contains unchanged existing
upstream proofs at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, together with a generated audit
driver. It has not been built in this environment either. Its delivered
verification is static import-closure and byte-integrity checking, not a fresh
validation of the upstream proof objects.

The separation of claims is:

| Item | Included | Verification performed here |
| --- | --- | --- |
| Existing upstream local Lean source closure | 216 unchanged modules plus exact pins | Import graph, byte identity, Git blob identity, SHA-256 |
| Existing-theorem axiom audit driver | `upstream/project/src/ExtractionAudit.lean` | Source inspection only; not elaborated or executed |
| Integral-series valuation-preserving specialization | Complete mathematical proof in the paper | Prose proof plus independent mathematical review |
| Sharper bounded-torsion nonvanishing | Complete mathematical proof and sharpness example in the paper | Prose proof plus independent mathematical review |
| Simultaneous determinantal/Fitting profiles and rank preservation | Complete mathematical corollaries | Prose proof plus independent mathematical review |
| Identification of the source's odd cocycles with a standard cohomological local kernel | Complete mathematical proof for odd coefficient primes and positive exponent | Prose proof plus independent mathematical review |
| A Lean proof of any new statement above | **Not included** | **Not performed** |

The proposed identifiers below describe a possible future formalization plan;
they are not existing declarations and are not included as `sorry`-containing
Lean skeletons.

## 1. Exact existing polynomial input

File:
`New/Congruences/Selmer/GeneralTheorem.lean`

Existing declaration:
`New.Selmer.exists_rootsOfUnity_ellVal_eval_le`

For a prime `ℓ`, a variable bound `s₀`, positive integer `m`, positive rational
radius `r`, a finite family of finite nonnegative valuation bounds `β i`, and
`ε>0`, it gives an integer `h₀` before any polynomials or points are supplied.
For integral polynomials in at most `s₀` variables and reference points of
coordinate valuation at least `r`, with evaluation valuations at most `β i`,
it supplies a single tuple `ζ` with:

- every `ζ u` of order dividing `ℓ^h₀`;
- `v(ζ u−1)≤r/m`;
- `v(P_i((ζ_u^j−1)_u))≤v(P_i(x_i))+ε` for all `i` and `1≤j≤m`.

The coefficient type is `New.intQpBar ℓ`, the integers in `PadicAlgCl ℓ`.
This is the algebraic closure, not its completion `ℂ_[ℓ]`.
`New.ellVal` is defined in `Lib/GaloisRep/Main/SelmerModules.lean`; it has
codomain `ENNReal`, agrees with the usual normalized nonnegative valuation
on integral elements, and sends zero to infinity.

The preceding source theorem
`New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`, in
`New/Congruences/Selmer/RootsOfUnity.lean`, is the one-exponent variant with a
total valuation budget. Its proof uses the explicit sufficient criterion

    m B + 1 < δ sum_{h=h_*}^H 1/(h+1),
    B = sum_i β_i,
    δ = min(ε,1)/(s₀+2),
    h_* = min{h≥1 : 1/φ(ℓ^h) ≤ r/m}.

A future formalization could expose this existing proof-internal bound as a
separate named theorem before extending the interface.

## 2. Integral formal-series extension with the same bound

Suggested new identifier:
`Transfer.exists_torsion_specialization_integral_series_same_bound`.

### Intended interface

Retain the exact parameters and a particular bound `H` satisfying the source's
polynomial property. Allow coefficients and reference points in completed
`ℂ_[ℓ]`, and replace integral polynomials by finitely many integral formal
series in finitely many variables. Assume every reference coordinate has
valuation at least `r>0` and each reference evaluation has finite valuation
at most its supplied budget. The output is exactly the same inequalities,
with exactly the same `H`.

### Necessary proof obligations

1. Define the ring of integral multivariable formal series over `ℂ_[ℓ]` and
   convergent evaluation on its open unit polydisc. Show evaluation is a ring
   homomorphism.
2. Prove the total-degree tail estimate: if all input valuations are at least
   `a>0`, the tail beyond degree `N` has valuation at least `(N+1)a`.
3. For every root of unity with order dividing `ℓ^H`, show that each nonzero
   `ζ^j−1` has valuation at least `1/φ(ℓ^H)`. A zero argument has infinite
   valuation and satisfies the same lower bound.
4. Show integral algebraic elements are dense in the integral completion and
   approximate finitely many series coefficients and reference coordinates
   simultaneously. Preserve the reference-radius bound by approximating to
   precision strictly greater than `r`.
5. Prove the nonexpanding property of integral polynomials on integral
   polydiscs, using a telescoping identity for monomials.
6. Choose a strict precision threshold greater than all `β_i+ε` and `r`;
   truncate uniformly over the entire bounded torsion grid before calling
   the source theorem.
7. Transfer all output valuations by the ultrametric equality
   `v(a−b)>v(a) => v(a)=v(b)`.

The degree-independent quantifier order is essential. Applying a theorem with
an order bound depending on a truncation degree and then taking a limit would
not establish this same-bound result.

## 3. Sharper nonvanishing without a valuation-loss target

Suggested new identifier:
`Transfer.exists_torsion_common_nonzero_linear_depth`.

### Intended interface

For finitely many integral formal series `F_i`, reference points whose
coordinate valuations are at least `r>0`, and total reference valuation at
most `B<∞`, put

    h_*(r) = min{h≥1 : 1/φ(ℓ^h)≤r},
    H = h_*(r)+floor(B).

There is a tuple of roots of unity with each coordinate of exact order
`ℓ^h` for some `h_*(r)≤h≤H`, on which every `F_i(ζ−1)` is nonzero.
For simultaneous nonvanishing at all powers `1≤j≤m`, the proved sufficient
depth is

    H = h_*(r/m)+floor(m B).

This is a weaker output than the preceding valuation-preserving theorem,
with a much sharper order-depth estimate. It is independent of the number
of variables. It does not assert the preceding ε-loss bound at this depth.

### Necessary proof obligations

1. Build the Banach algebra of bounded-coefficient series with the coefficient
   sup norm, with integral series as its closed unit ball.
2. Prove division by a monic polynomial `g=T^D+a`, where the coefficients of
   `a` lie in `ℓ Z_ℓ`, using the contraction
   `Q -> tail_D(f)-tail_D(a Q)`. This supplies integral quotient and
   remainder of degree less than `D`.
3. Iterate the division in finitely many variables. Preserve previously
   obtained degree bounds in the other variables.
4. For `g=product_{h=h_*}^H Φ_{ℓ^h}(1+T)`, prove that `g` is monic,
   `g≡T^D mod ℓ`, and its distinct roots are exactly the required torsion
   grid in one variable.
5. Prove multivariable interpolation: a polynomial of degree less than `D`
   in each coordinate vanishing on a `D`-point Cartesian grid is zero.
6. Define the radius-`r` Gauss valuation on integral series. Prove its
   multiplicativity, its monotonicity under evaluation at coordinate
   valuations at least `r`, and the ultrametric sum inequality.
7. Compute `v_r(g)=H−h_*+1=floor(B)+1`, which exceeds `B`. Grid vanishing of
   the product of the `F_i` would force Gauss valuation at least this number,
   contradicting its upper bound by the total reference valuation.
8. For the powers variant, produce `j`-th-root preimages of reference points
   of valuation at least `r/m`, substitute `(1+T)^j−1`, and use total budget
   `m B`. Existing source lemmas about such preimages can be reused.
9. Formalize the sharpness example for one variable, `m=1`: the product of
   the first `floor(B)` eligible shifted cyclotomic polynomials vanishes on
   every smaller allowed grid and has reference valuation `floor(B)` at zero.

This proof is inspired by the repository's degree-free torsion strategy but
does not use its final RH/GRH statements. It can be formalized independently
of the automorphic portion of the repository.

## 4. Determinantal/Fitting profiles and ranks

Suggested new identifiers:

- `Transfer.exists_torsion_determinantal_profile`
- `Transfer.exists_torsion_preserves_finitely_many_ranks`

### Intended interface

Take finitely many matrices over integral formal series. For each selected
matrix and minor size `k`, define `μ_k(x)` as the minimum valuation of its
`k`-minors. At reference points where that minimum is finite, choose a minor
attaining it. Apply the same-bound series theorem to these finitely many
witness minors to obtain

    μ_k(ζ^j−1) ≤ μ_k(x)+ε

simultaneously for every selected size and `1≤j≤m`.

For rank preservation alone, choose one maximal nonzero minor at each
reference point and use the sharper nonvanishing theorem with the sum of
their valuations. The output rank is at least each witness rank; it equals
the generic rank only when the witness rank was already generic.

### Necessary proof obligations

1. Formal evaluation commutes with finite determinants.
2. The finite set of minors attains its minimum whenever it is nonempty and
   not all determinants vanish.
3. Define the valuation of a finitely generated ideal of the valuation ring
   by its least-valuation generator; prove generator independence.
4. Connect `k`-minors with `Fitt_{u−k}(coker A)` for a `u×v` presentation.
5. Translate nonzero minors into lower bounds on rank.
6. If desired, prove Smith diagonalization for finite matrices over this
   valuation ring and identify `μ_k` with the sum of the first `k`
   invariant-factor valuations.

Only cumulative invariant-factor valuations are bounded. Individual factors
need not be bounded separately. Valuation is not ordinary module length over
the nondiscrete ring `O_{C_p}`. No arithmetic matrix presentation or comparison
with a Selmer group is supplied by this abstract corollary.

## 5. Source odd cocycles and standard cohomology

Suggested new identifier:
`Transfer.odd_cocycle_direct_limit_equiv_sha_eigenspace`.

### Existing source interfaces

`Lib/GaloisRep/Main/SelmerModules.lean` defines:

- `New.Selmer.tateTwist` with action `χ_ℓ^(−e)`;
- `New.Selmer.shaLocalSet`;
- `New.Selmer.shaOdd` as a module of actual locally constant cocycles,
  without quotienting by coboundaries;
- `New.Selmer.mem_shaOdd` exposing the defining local and parity conditions.

`New.exists_length_shaOdd_le` in `Lib/Cyclotomic/OddSha.lean` supplies a
single nonzero integer `X` of explicit size with a uniform bound on the
integral `O`-lengths of these finite-coefficient cocycle modules.

### Intended comparison

Fix an odd prime `ℓ`, positive exponent `e`, an allowed coefficient DVR `O`
with fraction field `F`, and a CM field `E` inside the specified cyclotomic
field. With transition maps multiplication by `ℓ`, the direct limit of
the finite cocycle modules is the natural complex-conjugation eigenspace

    Sha¹(E,(F/O)(−e))^{c=(−1)^(e+1)}.

Here `Sha¹` is the kernel of restriction to every local cohomology group.
This comparison is for divisible coefficients after passing to the direct
limit. It does not identify each finite cocycle module with a finite-level
standard Tate–Shafarevich group.

### Necessary proof obligations

1. Define continuous degree-one cocycles, coboundaries, cohomology, and the
   standard full local kernel, with coefficient twist and complex conjugation.
2. Prove that precomposition `Tz(g)=z(cgc)` fixes coboundaries. Since `2` is
   invertible, a `T`-odd class has the unique odd representative `(z−Tz)/2`.
3. At `v|ℓ`, identify the source kernel condition with restriction to
   `ker χ_ℓ` in the decomposition group. Prove
   `H¹(χ_ℓ(D_v),F/O(−e))=0` using a procyclic open subgroup and divisibility
   by its nonzero scalar `u^(−e)−1`.
4. At `v∤ℓ`, prove the unramified local cohomology is zero because
   `(Nv)^(−e)−1` is nonzero and acts surjectively on `F/O`.
5. Show each continuous cocycle from compact `G_E` to discrete `F/O` has
   finite image, hence lies at a finite coefficient level.
6. Include the coefficient action in natural complex conjugation: it is
   `(−1)^e T`, giving the stated eigensign `(−1)^(e+1)`.
7. Prove transition maps injective on actual cocycles. Uniform integral
   `O`-length bounds force eventual stabilization, so the same bound applies
   to the direct limit, and `X` annihilates it.
8. Deduce vanishing of integral odd cocycles by reducing modulo every `ℓ^n`
   and using the separatedness and torsion-freeness of `O`.

These statements are limited to odd `ℓ` and positive `e`. The proof does
not establish the corresponding assertions at `ℓ=2` or `e=0`, does not
identify any algebraic K-group, and does not prove Vandiver or an Iwasawa
characteristic-ideal equality.

## 6. Existing twisted-lattice interface

`New.TwistedLattice.covolume_add_index_nonneg`, in
`New/Reduction/Lattices/TwistedLattice.lean`, is already generic in the complex
vector space and twist type. Its conclusion is

    0 ≤ c + 2δ + (d−n)(b_short+b_denom) + b_volume.

It requires injective lifts, a completed basis, index certificates uniform
over allowed twists, conjugate norm bounds, and controlled heights of
determinant ratios. The paper extracts this existing interface and explains
its uses; it does not claim to have newly formalized it. Applying it to a
different arithmetic construction would require new proofs of its stated
input hypotheses, especially integrality, nonvanishing, and quantitative
denominator bounds.
