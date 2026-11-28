# Good labels: complete consumer audit and migration boundaries

Notation: this auxiliary audit uses `N` for the main report's `T`, the local-character order `q₂`, not the auxiliary level. It uses `B=q^(r/3)` as in the report.

Source: `VladimirReshetnikov/ProveIt`, commit
`89d12dd40424f1217fd818d84877b3da52396a3b`.
All source paths below are relative to
`Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/`.

## Conclusion

The full order `q^r - 1` of a primitive root is stronger than every downstream
consumer requires. A distinguished irreducible label can instead be selected by
a few norm power tests and one exclusion in the unique maximal proper
subfield. The resulting labels have an exact elementary count, and in the
repository's parameter regime they improve the relevant density from the
existing guaranteed order `1/(r^2 log q)` to at least `1/(4r)`.

This is a proved finite-field lemma and a reviewed migration plan, not an
implemented or elaborated Lean patch. The public congruence interface
`IsCommonRootPower`, the rank-one branch, and all conclusions beyond that
interface can be preserved exactly.

## Recommended predicate

Let `r = 3^a`, with `a >= 1`, let `3 | N`, and suppose `N^2 | q-1`. Write

\[
m=q-1,\quad B=q^{r/3},\quad M=q^r-1,\quad E=M/m,
\qquad n_p=v_p(N).
\]

For a nonzero element `alpha` of `F_(q^r)`, put `y = alpha^E`. Require:

\[
y^{m/3}\ne1,\qquad
y^{m/p^{n_p}}\ne1\quad(p\mid N,\ p\ne3),\qquad
\alpha^{3(B-1)}\ne1.
\tag{Q}
\]

The proposed polynomial predicate retains `IsLabel r c` and `Irreducible c`
and asserts that one root satisfies (Q). Its Frobenius conjugates then all
satisfy (Q). Retaining those two familiar conjuncts minimizes consumer edits;
the construction of counted polynomials proves them from (Q).

This recommended predicate is slightly stronger than the optional maximal
condition `v_p(orderOf y) > v_p(N)` for `p != 3`. The displayed power tests
have the advantages that no valuation of `q-1` occurs in the definition,
their counting density is independent of `q`, and their invariance under
normalization is a literal equality of powers.

### Why the norm tests suffice

The first test forces the full 3-primary order of `y`. For `p != 3` let
`h_p = v_p(m)`. The corresponding test implies

\[
v_p(\operatorname{ord}y)\ge h_p-n_p+1\ge n_p+1,
\]

because `h_p >= 2 n_p`. Hence `N | orderOf y`. Thus `y^x=1` implies
`N | x`, and therefore `N | j*x`, precisely the divisibility needed by
`IsCommonRootPower`.

### Why every prime-power image retains degree r

Put `z = alpha^(B-1)` and `C = B^2+B+1`. Then `z^C=1`. Since `B == 1 mod 3`,
`v_3(C)=1`. Furthermore

\[
z^{C/3}=\alpha^{M/3}=y^{m/3}\ne1,
\]

so the order of `z` is divisible by 3. The last test in (Q) is `z^3 != 1`;
therefore its order has a prime factor other than 3 as well. Its order is not
a prime power. For any prime `ell` and any `u >= 0`, it follows that
`z^(ell^u) != 1`. Consequently `alpha^(ell^u)` does not lie in
`F_(q^(r/3))`. All proper subfields of `F_(q^r)` lie in this one, since
`r` is a power of 3. Every such power has degree `r`.

This yields the existing `injOn_pow` conclusion, including `ell = 3`.
The full 3-primary norm and the separate last test are both essential to this
short argument. The tests are complementary, not redundant.

### Why normalization preserves the predicate

For `c in F_q^*` with `c^N=1`, replace `alpha` by `c alpha`. Its norm becomes
`c^r y`. Each exponent `m/3` and `m/p^(n_p)` is divisible by `N`, by
`N^2 | m` and `3 | N`. Therefore the norm power test values themselves do not
change. Also `c^(3(B-1))=1`, since `q-1 | B-1`. Thus (Q) is preserved.

All these conditions are invariant under Frobenius and finite-field
isomorphisms. A distinguished generator is used only to count; it is not
part of the predicate.

## Exact count

Let

\[
\delta_N=\frac23\prod_{p\mid N,\ p\ne3}(1-p^{-n_p}),
\qquad K=(B^2+B+1)/3.
\]

For a generator `g` of the group of order `M`, write `alpha=g^t`.
The norm tests say `3` does not divide `t` and `p^(n_p)` does not divide `t`
for the other primes. The last test says `K` does not divide `t`.
One has `gcd(K,q-1)=1`: modulo every prime other than 3 dividing `q-1`,
`K == 1`; modulo 3, the same follows by writing `B=1+3b`.
The Chinese remainder theorem therefore gives exactly

\[
\delta_N\bigl(M-3(B-1)\bigr)
=\delta_N(B-1)^2(B+2)
\]

qualified elements. Their Frobenius orbits all have size `r`, so the exact
number of qualified monic irreducible degree-`r` polynomials is

\[
P(q,r,N)=\frac{\delta_N}{r}(B-1)^2(B+2).
\tag{1}
\]

Every old primitive root satisfies (Q); the new class contains the old one.
For example, for `(q,r,N)=(19,3,3)`, `g^2` qualifies although its order is
`3429`, half of `q^r-1`; the new polynomial count is `1512`, versus `756`
primitive polynomials.

### Uniform repository bound, with no analytic totient estimate

`Parameters.q₂` in `New/Reduction/Data/FieldsAndPlaces.lean:175` is
`(P.q₀ * P.d)^(s+6)`. Thus its prime support is the fixed support of
`P.q₀ * P.d`, and every positive prime valuation is at least 6. Moreover
`3 | P.q₀` is available as `Parameters.three_dvd_q₀`, and
`Data.dvd_levelPrime_sub_one` supplies `q₂^2 | q-1`.

A finite product inequality gives

\[
\delta_N\ge\frac23\left(1-\sum_{p\mid N,p\ne3}p^{-6}\right)\ge\frac58.
\]

For the last inequality, `n^6 >= 16 n(n-1)` for `n >= 2`, so the finite sum
of `p^-6` is at most `1/16` times a telescoping sum of
`1/[n(n-1)]`, which is at most 1. No infinite series, prime distribution
estimate, or asymptotic estimate for Euler's totient is needed.

For `B >= 2`,

\[
\frac{M-3(B-1)}{q^r}
=1-\frac{3B-2}{B^3}\ge\frac12.
\]

Equation (1) therefore implies `P(q,r,N)/q^r >= 5/(16r) >= 1/(4r)`.
Fixed prime support is not needed for this uniform bound; the source
identity is recorded to rule out an unnoticed growing-support problem.

### Shorter formalization path: omit CRT and the exact polynomial count

The exact formula is useful explanatory information, but the implementation
needs only `P >= q^r/(4r)`. There is an even shorter route to that conclusion.
Work in the `M`-th roots of unity. The failures of the norm tests have at
most `M/3` and `M/p^(n_p)` elements respectively, and failure of the last
test has `3(B-1)` elements. These cardinality bounds follow directly from
the degree of `X^d-1`, or from the kernel size of a power map on a cyclic
group. For `B>=3`,

\[
\frac{3(B-1)}{M}=\frac{3}{B^2+B+1}\le\frac14.
\]

The union bound therefore leaves at least

\[
\left(1-\frac13-\frac1{16}-\frac14\right)M
=\frac{17}{48}M
\ge\frac{17}{64}q^r>\frac14q^r
\]

qualified roots. The source assumptions imply `q>=10`, so `B>=3` and
`M>=3q^r/4` are automatic. Apply the existing
`card_le_mul_card_image_of_maps_to` argument for the map `minpoly k`:
each polynomial has at most `r` roots. This gives the required lower bound
without formalizing CRT, the exact product density, or exact Frobenius
orbit cardinalities. The present source already uses precisely this
minimal-polynomial fiber argument in
`totient_le_mul_card_isPrimitivePolynomial`.

## Correct use of Green's weight: a subtle distinction

Let `w=(1-r/q)/q^r`, with `1<r<q`. Green's character degree bound is a
**lower** bound `w` for each label's idempotent coefficient. It does not
identify that coefficient with the uniform weight.

The existing proof bounds the uniform weighted count of **all monic
nonqualified polynomials**:

\[
(q^r-P)w\le1-P/q^r\le\exp(-1/(4r)).
\]

This is not an assertion that the actual Plancherel mass of the nonqualified
labels is at most this quantity. The distinction matters.

The existing allowed-label weighted count remains at least `1-epsilon`.
For a tuple of `f` factors, subtract the tuples containing no qualified
entry from the allowed tuples. The source's unchanged cover argument and
Green lower bound give

\[
\Re(1-e_{\rm good})(1)
\le f\varepsilon+\exp(-f/(4r)).
\tag{2}
\]

Thus the old sufficient condition

\[
2r(2r\log q+1)L\le f
\]

can be replaced by `4rL <= f`. Only `1<r<q` is needed here, not `q>=2r`.
With the repository's `L=9 logB`, the new numerical obligation is
`36 r logB <= f`. All other estimates in the bad-types-to-near-isometry
passage remain the same.

## Complete consumer map

An exact text search for `IsPrimitivePolynomial`, the two primitive-norm
helper names, and the primitive Frobenius-injectivity helper returns exactly
the following seven source files. Their uses were read in context.

| File | Current dependency | Required replacement |
|---|---|---|
| `New/UpperBound/Objects/LabelsAndIndexTypes.lean` | Definition at 54; scaling at 70; norm helpers at 91,101,113; good tuple witness at 143,149 | Add qualified predicate and its scaling theorem. Generalize the common norm-power identity to irreducible labels; replace full-order norm conclusion by `N | orderOf y`. Change only the distinguished witness in `goodTuples`. Allowed-label definition stays unchanged. |
| `Lib/LocalGL/Green/LabelCharacters.lean` | `injOn_Iio_pow_card_pow_of_isPrimitiveRoot` at 564 | Prove the same prime-power Frobenius injectivity from the order of `alpha^(B-1)` having at least two distinct prime factors. The new predicate establishes that premise by the short argument above. Green's character theory and its twisting theorem do not change. |
| `New/Spanning/MainTerm/BadTypes.lean` | Primitive count at 101; totient/log estimate at 162; tuple bound at 226 | Replace primitive count by (1), use the uniform bound and equation (2). The allowed-polynomial count and Green weight lemma remain unchanged. |
| `New/Spanning/Multiplicities/EqualMultiplicities.lean` | Witness extraction at 57; destructuring at 249 | Rename/generalize extraction. The consumer explicitly discards the primitive-root conjunct and uses only `IsLabel` and `Irreducible`, so its substantive trace proof is unchanged. |
| `New/Congruences/GaloisRepresentations/SelmerHypotheses.lean` | `IsLiftSetting.exists_primitive_or_one` at 598 | Replace primitive alternative by the new predicate parameterized by `q₂`. Preserve the `rank=1, c=X-1` alternative. |
| `New/Congruences/GaloisRepresentations/AttachedRepresentations.lean` | `isLiftSetting_descentPair` at 83, primitive extraction at 88 | Supply the new good-tuple witness. Rank-one `isLiftSetting_mainPair` stays mathematically identical. |
| `New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean` | `exists_isCommonRootPower_of_isPrimitivePolynomial` at 356; case wrapper at 450; witness extraction at 556 | Use new scaling, norm divisibility, and Frobenius injectivity. Return the **same** `IsCommonRootPower` structure. Nothing after this interface requires full primitive order. |

One additional direct numerical call site must be changed:
`New/Spanning/SecondMoment/SpanningTheorem.lean:220-242`,
`re_coeff_one_sub_goodIdempotentAbove_le`. Replace its `h_le_f` bound by
`4r(9 logB) <= f` and pass the rank/modulus hypotheses to the new counting
theorem. Its public conclusion stays `b^-8/2`; so do `bad_types_rare` and
the near-isometry theorem that consumes it.

The new projector is generally larger, because the distinguished-label set
is larger. Consequently this is a coordinated definition-and-proof refactor:
one must not apply the improved count while leaving the old primitive-only
`goodTuples` definition in place. All arguments using the new projector must
be rebuilt. Their audited mathematical inputs are unchanged, but a proof
that unfolds a changed definition can require routine elaboration edits even
when its theorem statement is preserved. The table is a consumer audit, not
a claim that only eight files can appear in the compiler's rebuild graph.

Searches for `goodTuples` and `goodTupleFamilies` were also checked. Additional
consumers in `New/Determinant/Chain/NormOfChain.lean` (456,502) and
`New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean` (506)
use only generic orthogonal-idempotent sums, range containment, or witness
extraction. They do not inspect primitive order. The `hyperplaneSum_mul_e₀`
argument in `LabelsAndIndexTypes.lean` extracts only the allowed-label
component.

## What is actually removable

The active proof no longer needs the primitive-polynomial count
`totient_le_mul_card_isPrimitivePolynomial`, the logarithmic-totient step in
`card_not_primitive_mul_le`, or the guarantee that a root generates the
entire multiplicative group of the degree-`r` extension.

`le_totient_mul_log` occurs outside its definition only in this counting
argument. The direct import of `Lib.Analytic.Primes` by `BadTypes.lean` can
therefore be removed after any elementary imported dependencies are supplied
explicitly. The whole `Lib.Analytic.Primes` file cannot simply be deleted:
`New/Reduction/Data/Existence.lean` still imports its other prime-existence
results. The new construction replaces one finite-field proof obligation;
it does not remove Green's theory, the rank-three-power choice, or
`q₂^2 | q-1`.

## Novelty against existing proposals

All 42 non-PDF text files in the five proposal directories were read and
recorded in `existing_proposals.md`; all 47 blobs including PDFs were verified
against the pinned checkout. Existing proposals alter spanning/translate
budgets, determinant completion or torsion grids, analytic prime-sum tails,
quadratic twist selection, or parameter sampling. None replaces the
primitive witness in the good-type projector, changes the norm-order
contract, or supplies this finite-field count. The present change composes
with those proposals because it preserves the allowed labels and the
downstream `IsCommonRootPower` interface.

## Checks and remaining implementation work

`../code/check_by_orders.py` is a pure-standard-library cyclic-group checker. Its
saved result `../checks/order_checks.json` records nine parameter sets, including
rank 9, and all of the following checks:

- Exact counts computed independently by summing `phi(d)` over qualifying
  element orders `d | q^r-1`.
- 319,653 exhaustive element exponents and 1,110,915 scalar-invariance checks.
- 772 prime-power degree checks, covering every relevant prime divisor of
  every qualifying element order in the selected cases.
- Counterexamples if the full 3-primary norm condition, the separate root
  exclusion, or the strict norm-order margin under scaling is omitted.

No finite test is a proof of the general theorem. The complete general
arguments are above. Remaining implementation is to formalize those
arguments, replace the eight local interfaces/call sites, and rebuild the
repository's terminal theorem while checking its axiom dependencies. A
successful Lean build has not been performed for this proposed refactor.
