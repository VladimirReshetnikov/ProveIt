# Endpoint counterexamples to universal common-base lifting

## Result and scope

For every integer k ≥ 1, the proposition `Section16ContextualLiftAt k` at commit `130fca9b1131fd983bd0af27565d36e8dfd2865a` is false. The counterexample satisfies the original weighted product property, all three structured-pair hypotheses, and every field of the actual common-base data structure. It works at γ = 1, with a fixed positive outer parameter θ depending only on k, at every sufficiently large prime modulus.

This is a counterexample to the universal choice of common-base witnesses in that precise interface. It does not refute Theorem 16.2, an existential large-piece assertion, or an existential version of contextual lifting. Indeed, the same input admits a second valid common-base witness whose good-domain graph is constant and does satisfy the unit-parameter conclusion. That second witness is constructed below.

The proof is in ordinary mathematics. No Lean code was compiled, no repository code was executed, and no upstream files were changed.

## What this adds to the earlier obstruction

An earlier unnumbered research note, *Sparse defects survive the recorded product-property interfaces* (7 October 2026), already gives a full-domain k=1 counterexample for each fixed 0<γ<1, with the stronger recorded Section 16 data. Its defect interval has length floor(N^(1/3)), so its relative density tends to zero. That result already warns against a universal implication from all those fields; the mere presence of a universal-witness obstruction is not claimed as new here.

The strengthening proved here reaches the exact endpoint γ=1, works in every k≥1, and places the balanced word on a slab of positive density bounded below by the fixed constant θ. The essential extra observation is the weighted graph-sumset lemma on a partial domain. Full-domain endpoint rigidity does not apply to that domain. The second, good witness makes the existential boundary explicit rather than merely leaving it logically open. The concentration method and finite-alphabet covering estimate are existing ingredients, not new discoveries.

## Pinned source frontier

Repository: VladimirReshetnikov/ProveIt. The branch was read at 2026-10-07 14:49 UTC and pinned to `130fca9b1131fd983bd0af27565d36e8dfd2865a` throughout this investigation.

- [Contextual contract, lines 17–27](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs16ContextualInduction.lean#L17-L27): after fixing θ, γ and a uniform modulus threshold, the asserted conclusion must hold for **every** `Section16CommonBaseData` witness D
- [Common-base fields, lines 32–54](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs16CommonBaseAssembly.lean#L32-L54): masses, induced selection, spectrum cover, common-base mass, and alternating identity
- [Product property, lines 52–63](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean#L52-L63): the lower bound is normalized by the ambient modulus N, even on a much shorter common domain E
- [Multiple-linearity definition, lines 46–69](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean#L46-L69): its conclusion is tested on every proper box, including boxes entirely inside E
- [Structured pair, lines 186–205](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean#L186-L205)
- [Existing finite-alphabet cover bound](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs16FiniteAlphabetBoxCover.lean): already proves the 5/16 bound for arbitrary proper box partitions
- [Existing balanced-word construction](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs16BalancedFieldWord.lean): the probabilistic ingredient used below is also proved in the repository
- [Actual common-base cover inputs](https://github.com/VladimirReshetnikov/ProveIt/blob/130fca9b1131fd983bd0af27565d36e8dfd2865a/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs16CommonBaseLineCovers.lean): these remain valid for both witnesses below

The complete downloaded source list, blob IDs, and pin are recorded in the adjacent `source_manifest.json`. All 35 complete local Lean snapshots were verified byte-for-byte against their pinned Git blob IDs. At 15:03 UTC main had advanced to `e40a57b9878f2b20636fe7d1acdc3b2e61796e87`; a fresh connector read confirmed that the contextual contract, common-base structure, Section 16 definitions, product-property definitions, and common-base line-cover file have identical blob IDs. The intervening work adds polynomial-localization constructions and does not assert the contextual lifting contract.

## Constants and construction

Fix k ≥ 1 and put d = k + 1. Define

    A_j = 2^(2^(j+8))
    K = 2^A_d = multipleQ(1/2, 1, d)
    a = 1/K = multipleC(1/2, 1, d)
    R = 4K
    θ = 1/(8R) = 1/(32K)
    γ = 1
    N_* = (2^26 K^6)^(2K).

These are fixed finite constants once k is fixed; K, R and N_* are integers. Let N ≥ N_* be prime, and work in F_N. Set

    L = floor(N/(4R))
    E = {0, 1, ..., L-1} ⊂ F_N
    S = {0, 1, ..., R-1} ⊂ F_N
    α = L/N.

All displayed intervals are embedded injectively, and

    θ = 1/(8R) ≤ α ≤ 1/(4R).

Choose f : F_N → S with the following balance property: for every proper modular arithmetic progression T of length at least N^(1/(2K)), and every c ∈ F_N,

    |{x ∈ T : f(x)=c}| ≤ β |T|,
    β = 1/R + 1/(32K) = 9/(32K).

The next section proves that such f exists for every N ≥ N_*. Define

    B = F_N^k × E
    φ(h,x) = f(x).

Use the displayed function on the entire ambient space, as required by the Lean interface; only its graph over B matters for the product property.

## Balanced words with an explicit threshold

Choose the values f(x) independently and uniformly from S. For any proper progression T of n distinct points, each symbol count is a sum of n independent Bernoulli variables of mean 1/R. With ε = 1/(32K), Hoeffding's inequality gives an upper-tail probability at most

    exp(-2 ε² n) = exp(-n/(512K²)).

There are at most N²(N+1) ≤ 2N³ presentations of proper modular progressions, including all lengths from 0 to N, and R possible symbols. Thus the probability of any violation on a progression of length at least t = N^(1/(2K)) is at most

    2 R N³ exp(-t/(512K²)).

Because N ≥ N_*, t ≥ 2^26 K^6 and sqrt(t) ≥ 8192K³. The elementary inequalities log(t) ≤ sqrt(t) and log(8K) ≤ 8K give

    512K² log(2 R N³)
      = 512K² log(8K) + 3072K³ log(t)
      ≤ 4096K³ + 3072K³ sqrt(t)
      ≤ t/2 + 3t/8
      = 7t/8 < t.

The union bound is strictly less than one. Hence a balanced word exists. Values outside S have zero occurrences, so the assertion holds for every c ∈ F_N.

The same threshold also guarantees N ≥ (8R)² and t ≥ 32KR. Consequently

    W := L^(1/K)
       ≥ (N/(8R))^(1/K)
       ≥ N^(1/(2K))
       ≥ 32KR.

These are the exact width inequalities needed later.

## The genuine unit product property

The following elementary weighted-energy fact supplies the missing hypothesis that invalidated the earlier full-domain finite-alphabet example.

**Weighted graph-sum lemma.** Let A,S ⊂ F_N and g : A → S. If |A+A| |S+S| ≤ N, then for every F ⊂ A and every nonnegative weight w on F,

    Σ_{x₁+x₂=x₃+x₄, g(x₁)+g(x₂)=g(x₃)+g(x₄)}
       w(x₁)w(x₂)w(x₃)w(x₄)
      ≥ N^(-1) (Σ_{x∈F} w(x))^4.

All four variables in the sum lie in F. To prove it, let r(u,v) be the weighted number of pairs (x,y) ∈ F² with x+y=u and g(x)+g(y)=v. Then the left side is Σ r(u,v)², whereas Σ r(u,v)=(Σ w)². The support of r has at most |A+A||S+S| elements. Cauchy–Schwarz proves the claim. Zero total weight is harmless and can be treated separately.

For our intervals,

    |E+E||S+S| ≤ (2L-1)(2R-1) < 4LR ≤ N.

Now check every part of `HasProductProperty B φ 1`:

1. In the final coordinate, all parallel restrictions are the same function f on E. For any positive number of restrictions, their simultaneous additivity condition is exactly the single graph-additivity condition in the lemma. Every permitted common domain F lies in E. The lemma gives the required lower bound, since γ^(8p)=1
2. In any of the first k coordinates, every restriction is constant as a function of the varying coordinate. Every additive quadruple automatically respects all these constants, however many restrictions are chosen. Weighted additive energy in F_N is at least (Σw)^4/N by Cauchy–Schwarz on ordinary pair sums
3. With zero restrictions, in any direction, the simultaneous condition is empty. The same ordinary weighted additive-energy bound applies

Thus the original weighted product property holds at parameter exactly one. It is not being inferred from a finite-alphabet cover or from the two previously refuted lifting premises.

Moreover Γ = graph(φ|B) itself has `RelationProductProperty 1`, because every contained partial graph is a restriction of this one. It has |Γ|=α N^d ≤ N^d, and, at the displayed threshold, its projection has density α > θ. Thus the example also satisfies the natural relation-size bound and lies on the non-small-projection side of the surrounding extraction argument.

## All three structured-pair conditions

Write

    θ₁ = (θ/4)^(2^(2^(k+5)))
    s₀ = multipleS(2^(-(k+2)) θ, 1, k)
       = (2^(k+3)/θ)^(2^(2^(k+6))).

We have 0 < θ₁ ≤ θ^16 ≤ α^16 and s₀ ≥ 1/θ ≥ R.

**Proper cross-sections.** Every coordinate-face pullback of φ is S-valued, in every dimension l < d, including l=0. It is covered on its entire domain by the R constant multilinear maps with values in S. For any loss parameter 0 < ρ ≤ 1, the graph budget is

    multipleQ(ρ/s₀,1,l)^s₀
      = (s₀/ρ)^(A_l s₀) ≥ R.

Use the original proper box as a one-cell partition and take the good set to be its whole carrier. The width exponent (ρ/s₀)^(A_l s₀) lies in (0,1], so the original width meets the required lower bound. This proves exactly `ProperCrossSectionsMultiplyLinear 1 s₀ B φ`, with the source's common parameter.

**Arrangement count.** A contained 8-arrangement has an arbitrary common side in F_N^k, sixteen arbitrary cube bases in F_N^k, and sixteen final coordinates in E satisfying the additive eight-versus-eight relation. If T₈(E) counts those additive 16-tuples, then

    generalArrangementCount 8 B = N^(17k) T₈(E).

Cauchy–Schwarz applied to the N possible eightfold sums gives T₈(E) ≥ L^16/N. Hence the arrangement count is at least

    α^16 N^(17k+15) ≥ θ₁ N^(17k+15),

exactly as required.

**Respected arrangements.** Every k-dimensional cube in a fixed final-coordinate section has alternating φ-value

    f(x) Σ_{e∈{0,1}^k} (-1)^|e| = f(x)(1-1)^k = 0,

using k ≥ 1. Therefore every arrangement is respected, and in particular the required proportion 1−2^(-44) is met.

## Every common-base field for the bad witness

Take

    H = J = F_N^k
    Y_h = every element of section16CubeDomain(B,h)
    φ′(h,x) = 0
    x₀ = 0.

For every h, the cube domain is exactly the set of arbitrary bases a ∈ F_N^k paired with x ∈ E, and its cardinality is N^k L = α N^(k+1). The all-selected good domain at any common base is therefore B itself. In particular

    B₁ = section16GoodDomain(B,H∩J,Y,0) = B
    φ₁ = section16PhiOne(φ,0) = φ
    good-pair count = α N^(k+1).

Here are all fields of `Section16CommonBaseData`, with no appeal to a future lifting theorem:

- **Hmass:** θ₁/4 ≤ 1, while |H|=N^k
- **intersect_mass:** θ₁/8 ≤ 1, while |H∩J|=N^k
- **cube_mass:** θ₁/4 ≤ α, while each cube domain has α N^(k+1) elements
- **selected_mass:** Y_h is the entire cube domain, and 2^(-27) θ₁^6 ≤ 1
- **selection, value clause:** every selected cube has induced alternating value zero, equal to φ′
- **selection, Bohr/progression clause:** the zero function is globally affine; therefore its restriction to every stipulated progression/domain is affine, independently of the Bohr set and the value of ζ
- **spectrum:** the next paragraph supplies the required actual spectrum relation and cover
- **good_mass:** θ₂ = 2^(-32) θ₁^8 ≤ α, so the exact good-pair count meets the specified lower bound
- **identity:** the alternating cube identity is zero. Solving it for the all-ones term gives precisely φ₁ = (−1)^k φ′ + φ_remainder on B₁, the source's corrected identity

For the spectrum field, the indicator of B depends only on x. Thus for every h the source's higher cube correlation is

    higherCubeCorrelation(1_B,h)(x) = N^k 1_E(x).

Let δ = 2^(-37)(θ₁/4)^(11/2), and put

    K_spec = {r ∈ F_N : |hat(1_E)(r)| ≥ δN}.

Then the actual spectrum relation is F_N^k × K_spec, independently of h. The source uses the unnormalized Fourier transform. Parseval gives

    |K_spec| δ²N² ≤ Σ_r |hat(1_E)(r)|² = NL ≤ N²,

so |K_spec| ≤ δ^(-2). Put t = δ^(-2) multipleS(θ₁/8,δ,k), exactly as in the source. We have 0<δ≤1 and t≥1. For any 0<ρ≤1,

    multipleQ(ρ/t,δ,k)^t
      = (t/(δρ))^(A_k t) ≥ δ^(-2),

because A_k t≥2. Cover the spectrum relation by its |K_spec| constant graphs, keep the whole input box as the sole cell, and discard nothing. Its width exponent (δρ/t)^(A_k t) is in (0,1]. This proves the exact `MultiplyLinear δ t` spectrum field. Taking J=F_N^k does not alter that relation.

Thus D_bad is a genuine instance of the common-base structure. In particular the already proved `D.lifting_cover_inputs` theorem also supplies the genuine line and final-section covers; they are not substituted for the upstream hypotheses.

## Failure of the required unit cover

Consider the proper box P = E^d, with every axis the ordinary step-one interval E. Its width is L and its carrier lies entirely in B₁=B.

Suppose `MultiplyLinearFunction 1 1 B₁ φ₁` held. Test its definition at loss ρ=1/2 and this box. It would provide a proper box partition (Q_j), a good set G ⊂ P with |G| ≥ |P|/2, and q multilinear maps per cell, where

    q ≤ K
    width(Q_j) ≥ L^(1/K) = W.

Fix a cell and fix its first k coordinates h. On the last-coordinate axis T of that cell, each of these multilinear maps is an affine function of x. Properness gives |T| equal to the formal axis length, hence |T|≥W≥N^(1/(2K)).

- A constant affine function agrees with f on at most β|T| positions, by balance
- A nonconstant affine function is injective over the field, so it agrees with the S-valued f on at most R positions

The union of q affine graphs therefore covers at most

    q(β|T| + R)
      ≤ (Kβ + KR/W)|T|
      ≤ (9/32 + 1/32)|T|
      = (5/16)|T|.

Sum over all initial-coordinate fibres of the cell, then over the disjoint partition cells. Every point of G requires a cover because P ⊂ B₁. Thus |G|≤5|P|/16, contradicting |G|≥|P|/2. The box is nonempty, so the contradiction is strict.

This bound allows each partition cell to have its own common difference and its own candidate maps. It treats every proper modular progression, including wrapping progressions. It therefore does not restrict the conclusion to a fixed or chosen product partition.

For the fixed θ and γ constructed above, every prime N≥N_* has such an input and bad witness. Primes are unbounded, so no threshold N₀ in `Section16ContextualLiftAt k` can make its universal assertion true. This proves the stated negation for every k≥1.

## A good witness for the same input

The quantifier distinction is substantive. Choose c∈S with

    E_c = {x∈E : f(x)=c},     |E_c|≥L/R.

Keep the same B, φ, H, J, φ′, x₀ and actual spectrum data, but replace Y_h by the cubes whose final coordinate lies in E_c. Call the resulting witness D_good. The selected fraction of every cube domain is at least 1/R. Since

    2^(-27) θ₁^6 ≤ 1/R,

the selected-mass field still holds. The value and Bohr clauses still hold for φ′=0. The new common-base good-pair count is N^k|E_c|≥(α/R)N^(k+1), and

    θ₂ = 2^(-32) θ₁^8 ≤ θ/R ≤ α/R.

Every other common-base field is unchanged, and the alternating identity still holds. Consequently D_good is also valid, but now

    B₁_good = F_N^k × E_c,

and φ₁ is identically c on this domain. One constant multilinear graph, the original input box, and no exceptional set prove `MultiplyLinearFunction 1 1 B₁_good φ₁` directly.

Therefore this construction supplies both a bad and a good compatible witness for one structured input. It positively demonstrates why the universal contract is too strong and why its failure does not refute an existential replacement.

## A precisely delimited next interface

The surrounding induction only needs a sufficiently large unit-multiply-linear subrelation. One precisely sufficient replacement keeps the quantifiers over admissible θ, γ, a uniform modulus threshold, all later prime N, and all B, φ with product and structured-pair properties, but replaces the final clause by

    there exists D : Section16CommonBaseData θ γ B φ
    such that MultiplyLinearFunction γ 1 (GoodDomain D) (PhiOne D).

If this existential contract were proved, the present large-piece argument would choose that D directly and transport its already specified good mass and unit cover back to the original relation. Only the extraction threshold and the new existential-lifting threshold would be needed at this step; there is no need to first construct an arbitrary D and then cover every possible choice. This conditional implication follows directly from the existing mass-transport argument, and does not assert the missing existential contract.

Another possible replacement could permit a further subdomain of a selected translated good domain with an explicitly proved mass loss. This note does not prove either replacement in general.

The unresolved general task is therefore to construct a witness or an additional restriction with both the required density and unit cover, not to prove the existing universal `Section16ContextualLiftAt`. The already verified line covers and remainder covers remain usable, but they cannot make that universal quantifier valid: D_bad satisfies those covers too.

This also identifies the structural reason that adding the product property did not repair the universal interface. The product property is normalized at the ambient scale N; a short input interval can absorb finite alphabet complexity into a small graph sumset. Unit multiple-linearity must then succeed on boxes entirely inside that short interval, with a graph budget independent of its density. A carefully selected colour class repairs this example, while selection with no additional loss does not.
