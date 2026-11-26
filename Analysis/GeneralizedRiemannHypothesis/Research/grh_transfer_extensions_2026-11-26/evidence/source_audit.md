# Source audit: what is reusable in `grh-lean`

## Snapshot and verification status

The local clone `/workspace/scratch/f18d54354637/sources/grh-lean` was verified by `git rev-parse HEAD` and `git status --porcelain`: it is clean at
`72fead102f663d5c7a407964a13dc0cf9d977207`. The root agent independently obtained the same SHA from GitHub. All references below are relative to this repository and this commit.

The readable edition has exactly **803 tracked Lean source files and 477,124 total source lines**: 495 `Lib` files, 306 `New` files, `Main.lean`, and `Statements.lean`. The compact edition has 794 files and 112,827 total source lines. These are physical line counts, including comments and blank lines, not mathematical code-size estimates. The pinned toolchain is Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The earlier figure of 216 modules describes a selected extraction, not the whole readable edition.

This audit read source; it did **not** rebuild the upstream project or run Lean's kernel on it. The repository README reports successful compilation, the standard axiom list, and acceptance of an export by independent checkers. These remain upstream-reported checks, not checks newly performed here.

## 1. Exact theorem scope

`grh/src/Statements.lean`, lines 6–16, quantifies over `DirichletCharacter ℂ N`. `grh/src/Main.lean`, lines 4–22, exports five theorems: RH, the equivalent statement about nontrivial zeta zeros, Dirichlet nonvanishing to the right of one half, Dirichlet zeros on the line, and its primitive-character specialization. The code covers all positive moduli and imprimitive characters as well. There is no exported Artin-, general Hecke-, or automorphic-GRH theorem here.

This scope matters independently of the status of RH/Dirichlet GRH. A nonabelian transfer has to add a new arithmetic construction or new estimate; changing the name of the character is insufficient.

## 2. The transferable determinant interface

The most reusable architecture is explicit in `grh/src/New/Reduction/MainInequality.lean`, lines 7–16 and 87–156. Let `d` be the target dimension, `n` the number of independent chosen vectors, `H` the main amount, `R` the prime remainder, and `m` the number of lifts. The upper and lower bounds compare the **same** covolume, corrected by twice its index. Schematically,

\[
d(H-E_-)
\le \log\operatorname{Gram}(y)+2\delta
\le n(H-mR+E_+)+2\delta.
\]

The main amount cancels after the needed sign and rank controls. The theorem in this source is

\[
m\,\mathrm{totalRemainder}\le f a(\log b)^5.
\]

Its inputs are genuine, separate mathematical requirements:

* **Short integral forms.** `span_short_integralRamified_eq_top`, `New/Reduction/ShortAndEnough.lean` 254–257, supplies a spanning collection whose squared norms are at most `exp(H-mR+f a log⁴ b)` at every complex conjugate.
* **Controlled index.** `indexLe_normalizedPoincare`, the same file 373–375, bounds the index by `#t · dim(source) · 2 f a log³ b`.
* **Almost complete spanning with few translates.** `enough_forms`, the same file 448–452, gives positive target dimension, `#t dim(source) ≤ 5 d log(1+2b²)`, and span dimension at least `(1-4/b²)d`.
* **Matching lower bound.** `integral_forms_long`, `New/Determinant/Twist/LongForms.lean` 214–217, gives `d(H-3 f a log⁴ b) ≤ c+2δ` for the chosen independent vectors.

The underlying lower-bound theorem is already abstract. `TwistedLattice.covolume_add_index_nonneg`, `New/Reduction/Lattices/TwistedLattice.lean` 477–488, assumes injectivity of all lifts, a basis made of `n` chosen vectors and `n'` completion vectors, integrality and shortness of the completion vectors, and height bounds for a scalar denominator and a ratio of lift determinants. It concludes

\[
0\le c+2\delta+n'(b_{\rm short}+b_{\rm denom})+b_{\rm volume}.
\]

This theorem is reusable outside the particular RH construction. Its arithmetic inputs are not automatic. In particular, the index definition at lines 156–164 uses a matrix that works for **all allowed twists at one prime**. One cannot choose a separate correction matrix for every twist and still cite this definition.

Conversely, the lower-bound theorem deliberately allows **one twist for each prime**. A single global twist for all primes is not required. What binds those choices is the height comparison for the family of determinant ratios. The rational Gram matrix, compatible conjugate integral lattices, and nonzero determinants are part of the structure, not expendable notation.

The final analytic step `eventually_primeRemainder_le_rpow`, `New/Reduction/OneSidedBound.lean` 200–202, is the one-sided bound `R(y)≤y^{-1/2+ε}`. `grh`, lines 239 onward, combines this with a zero criterion and a quadratic auxiliary twist. Thus a new nonabelian instance must connect its Frobenius-sensitive remainder to a matching shortness/divisibility/volume construction.

## 3. The full divisible Selmer group really is controlled

The finite-precision objection in some earlier discussions is too broad for this source.

`New/Congruences/Selmer/Line.lean` 120–144 defines `divisibleSelmer`, `divisibleLength`, and `TwistedLengthLe` using coefficients

\[
\operatorname{Frac}(O')/O',
\]

not merely a selected quotient `O'/ℓ^M`. The `TwistedLengthLe` predicate holds over all sufficiently large coefficient rings containing the character, with lengths normalized by `length(O'/ℓ)=1`.

The key passage from finite level to the whole module is explicit in the same file, 81–94:

\[
\operatorname{length}_O\operatorname{Sel}(O/a)<v_O(a)
\quad\Longrightarrow\quad
\operatorname{length}_O\operatorname{Sel}(\operatorname{Frac}(O)/O)
\le\operatorname{length}_O\operatorname{Sel}(O/a).
\]

The hypothesis is a **strict threshold**. This is why one well-chosen finite level suffices. Lines 433–465 apply the principle when the value of a bounding determinant polynomial has valuation less than `M`.

### Elementary stopping lemma behind the code

Let `O` be a DVR with uniformizer `π`, let `X` be any torsion `O`-module, and let `N≥1`. If

\[
\operatorname{length}_O X[\pi^N]<N,
\]

then `X=X[π^N]`; hence `X` has the same finite length. Indeed, if `π^N x≠0`, choose the least `r>N` with `π^r x=0`. The element `π^{r-N}x` has exact order `π^N`, so the cyclic module it generates, of length `N`, embeds in `X[π^N]`, a contradiction. No finite-generation hypothesis on `X` is necessary. For the cocycle module, local constancy on the compact Galois group implies finite image, so every cocycle has a common denominator and the module is torsion. The source proves this at lines 62–79.

The general endpoint `exists_anticyclotomic_twist`, `New/Congruences/Selmer/GeneralTheorem.lean` 392–396, produces **one character** `ψ` and one auxiliary set `Q` for which every `ψ^j`, `1≤j≤m`, obeys all the finite family of Selmer and special-value bounds simultaneously. `IsSmallTwist.length_le`, lines 55–76, uses the full predicate above. The specialized endpoint `exists_mFoldTwist_hasDivisibleSelmerLengthLe`, `New/Congruences/Selmer/TwistingTheorem.lean` 370–383, again names the full divisible coefficient bound. It is not merely a statement of the form `∀M ∃ψ_M`.

### What still has to be checked for an arithmetic application

`SelmerDatum`, `New/Congruences/Selmer/SelmerData.lean` 105–151, includes substantial hypotheses:

1. A nonzero-rank lattice whose residual image spans the full matrix algebra.
2. Finite local cocycle modules and the stated sum-of-local-ranks budget.
3. Finite global conjugate-dual congruence defect and finite local and first-prime defects.
4. An inertial element `γ` away from `ℓ` acting by the same scalar `ζ` as its conjugate inverse, with `ζ²−1` a unit.
5. The actual local conditions and ramification set needed by the arithmetic group being studied.

The global defect is the supremum, over finite coefficients, of lengths of `Hom_G(W,W^{*c})`, and `β` also includes local defects and valuations of `det(ρ(g₀)-1)` and its conjugate-inverse counterpart. These are defined at lines 59–96 and 163–179. A rational conjugate self-duality can make the global supremum infinite. Ordinary polarized elliptic-curve representations therefore cannot simply be inserted without revising or satisfying these hypotheses.

Small **normalized** length does not imply vanishing. Over a coefficient ring of absolute ramification index `e`, a nonzero length-one module has normalized length `1/e`. The character used in the theorem can enlarge `e`. Finiteness, vanishing, exact orders, and equality with the intended arithmetic Selmer group are separate conclusions.

### Normalized cocycles versus cohomology classes

Counting cocycles is not itself an obstruction when the scalar normalization is available. For any group `G`, a `G`-module `M`, and `γ∈G` such that `ρ(γ)-1` is an automorphism of `M`, each class in `H¹(G,M)` has a unique representative satisfying `z(γ)=0`: subtract the coboundary of `(ρ(γ)-1)^{-1}z(γ)`. The uniqueness follows by evaluating a coboundary at `γ`. Any Selmer conditions preserved by coboundaries descend through this isomorphism. The source's `ζ-1` unit condition supplies precisely this invertibility. Identifying its local relations with a desired classical Selmer group must still be proved.

## 4. Torsion specialization already has strong simultaneous quantifiers

`exists_rootsOfUnity_ellVal_eval_le_add`, `New/Congruences/Selmer/RootsOfUnity.lean` 474–485, says that for fixed variable-count bound `s₀`, radius `ρ>0`, total valuation budget `β`, and tolerance `ε>0`, there is one `h₀` such that **every finite family of integral polynomials**, each with its own witness point of coordinate valuation at least `ρ`, and with total witness valuations at most `β`, admits a common tuple of roots of unity of orders dividing `ℓ^{h₀}`. At that common tuple every polynomial's valuation increases by at most `ε`. The bound does not depend on the degrees of the polynomials.

Thus the source is stronger than independent existence of a good point for each polynomial. However, it is a theorem about polynomials over the integral closure of `ℤ_ℓ` with bounded witness budget. A proposed extension to analytic functions must verify integral/bounded coefficients and a legitimate limiting argument. It cannot include arbitrary unbounded-coefficient series such as the logarithm without additional hypotheses.

## 5. Odd cocycles, K-theory, and parity

The exact theorem `exists_length_shaOdd_le`, `Lib/Cyclotomic/OddSha.lean` 645–651, assumes a CM number field `E` contained in `Q(μ_N)`. It provides a nonzero integer `X` bounded by

\[
X\le 2^{4(N+t+3)^{27}} h_E
\]

whose valuations bound the stated finite-level odd-cocycle modules simultaneously in the prime, the coefficient ring, every twist exponent `e<t`, and every torsion exponent. The field and twist range are fixed before `X` is chosen. This does not yield a uniform vanishing result while the field or conductor grows.

The source's `shaOdd` is defined in `Lib/GaloisRep/Main/SelmerModules.lean` 174–186. For `e≠0`, it imposes `z(cgc)=-z(g)` on a Tate twist `(-e)` and special local conditions. Under the usual cohomological action, the coefficient action of `c` contributes `(-1)^e`, so the resulting class has sign `(-1)^{e+1}`. For `e=0` the parity condition is absent. This is why one must explicitly compute the arithmetic eigenspace rather than matching the word “odd” to an independently defined object. At `ℓ=2` one also cannot freely split eigenspaces using division by 2.

The repository itself explicitly says that the even classes where Vandiver's conjecture lives do not enter its denominator bound (`New/Congruences/FirstOrder/DenominatorBound.lean` 44–47). There is no source theorem identifying a particular new algebraic K-group with one of these modules or proving a new K-group vanishes. Such a transfer needs an exact arithmetic comparison and a valid vanishing or determinant certificate; these are additional mathematical work.

## 6. A concrete next transfer, and the exact new work

The abstract determinant theorem is suitable for a **nonabelian Frobenius-weighted theta construction**. An attainable first research target is a fixed dihedral/`S₃` Hecke factor, with explicit finite-group prime detector. This is a method transfer rather than a consequence of the exported Dirichlet GRH theorem. A completed transfer would require:

* an integral theta or algebraic-form construction whose local derivative divisibility is the desired Frobenius detector;
* a uniform shortness and almost-full-spanning estimate for those forms, including the cost of translating and completing the span;
* injective lifts and a determinant identity with the same main term and a compatible arithmetic period normalization;
* Selmer/congruence and special-value bounds strong enough to keep the denominator budget below the required square-root scale;
* a zero criterion that controls cancellation among the relevant Artin/Hecke factors.

The source already provides abstract interfaces for the latter determinant comparison and for a significant part of the twisting machinery. It does not supply the first Frobenius-sensitive divisibility estimate. Substituting a nonabelian CM base also leaves the `E⊂Q(μ_N)` hypothesis of the odd-cocycle estimate unresolved.

A more focused preparatory extension is to adapt the **general** twisting theorem to a selected finite-image Artin lattice, rather than trying to use the highly specialized `IsMainSummandLike` endpoint. A useful source lemma is `congruenceTerm_le`, `SelmerData.lean` 692–695. If an element `g` acts trivially on both `T` and its conjugate and `1−χ_cyc(g)` is a unit, it gives global defect zero. For a finite-image representation unramified at a suitable prime `ℓ`, local inertia can often supply this element. This removes one concrete obstruction, but the scalar inertial normalization, the local rank budget, ramification terms, and the link to the desired arithmetic objects must all still be established. This is a proposed research program, not a new claimed solution of Artin GRH, BSD, Bloch–Kato, or Vandiver.

## Canonical source links

All source paths above are at
`https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/`.
The machine-readable companion `provenance.json` records exact blob and SHA-256 hashes for the audited files and a declaration-level index.
