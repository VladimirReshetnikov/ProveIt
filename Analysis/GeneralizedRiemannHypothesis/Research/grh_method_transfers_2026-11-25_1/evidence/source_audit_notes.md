# Independent source audit and arithmetic transfer results

## Provenance and scope

Source: `lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207` (commit timestamp 2026-11-25 20:38:07 UTC). The readable edition pins Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

`grh/src/Statements.lean` imports only `Mathlib`. Its exact public propositions are:

```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

`grh/src/Main.lean` exports `riemannHypothesis : RiemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive`, with the four custom types above. Thus the word GRH in this repository is specifically Dirichlet GRH, including imprimitive characters; the public statements do not assert arbitrary Dedekind, Hecke-over-number-fields, Artin or automorphic GRH.

The repository README reports successful independent checker runs (nanoda, con-leche, con-ron) and Comparator, and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. These are repository-reported checks. This audit inspected source and did not independently rebuild the 300,000-line development.

## The proof mechanism

The core is arithmetic geometry, not simply a generic analytic zero criterion. The relevant files and declarations are:

| Ingredient | File below `grh/src` | Declaration |
|---|---|---|
| Short integral forms | `New/Reduction/ShortAndEnough.lean` | `New.Data.span_short_integralRamified_eq_top` |
| Small index | same | `New.Data.indexLe_normalizedPoincare` |
| Few translates span almost all target space | same | `New.Data.enough_forms` |
| Product formula with independently selected local twists | `New/Reduction/Lattices/TwistedLattice.lean` | `New.TwistedLattice.covolume_add_index_nonneg` |
| Integral forms are long | `New/Determinant/Twist/LongForms.lean` | `New.Data.integral_forms_long` |
| Main cancellation | `New/Reduction/MainInequality.lean` | `New.star_inequality` |
| One-sided error bound | `New/Reduction/OneSidedBound.lean` | `New.eventually_primeRemainder_le_rpow` |
| Zero-free half-plane from one-sided bound | `New/Reduction/Zeros/Criterion.lean` | `New.LFunction_ne_zero_of_primeRemainder_le` |

Theorem A constructs integral vectors with small archimedean norm and controls their index. Theorem B gives a family of dimension at least `(1 - 4/b^2)` times the target dimension. Theorem C bounds its covolume plus twice the index from below. Abstractly the comparison is

\[
M - \text{error} \le (V+2\delta)/d \le M - (n/d)mR+\text{error}.
\]

The common main term M cancels. With the actual source normalizations this yields

\[
m\operatorname{totalRemainder}\le f a(\log b)^5,
\]

and then

\[
R_{q_0}(x)\le\varphi(q_0)(\log b)^6/m+|R_{q_0}(x_1)|+\log b\,|R_1(x_1)|.
\]

Here `m` is between `sqrt(x)` and `2 sqrt(x)`, `log b <= 2x^epsilon`, and `log x_1 >= x^(epsilon/12)`. The ordinary prime number theorem controls the two enormous-cutoff terms and gives an eventual upper bound `R(x)<=x^(-1/2+epsilon)`.

The analytic criterion also chooses an auxiliary quadratic character whose twisted L-functions have no zeros in a specified box. This removes cancellation in the residues of logarithmic derivatives. The source uses `Lib/Analytic/QuadraticTwist.lean`, `exists_entireL_quadTwist_ne_zero`. A transplant to GL(2) would require an appropriate zero-free auxiliary family and new arithmetic estimates, not just relabeling L-functions.

The genuinely reusable local-to-global interface is the twisted lattice theorem. For an injective family of lifts and an almost-basis completed by `n'` auxiliary vectors, it proves

\[
0\le c+2\delta+n'(b_{\rm short}+b_{\rm denom})+b_{\rm volume}.
\]

The finite-place twist may depend on both p and the embedding into an algebraic closure of Q_p. It is not a claim that one global twist simultaneously works at all primes. Keeping that quantifier order is essential.

## A more portable internal theorem: degree-independent torsion selection

File: `grh/src/New/Congruences/Selmer/RootsOfUnity.lean`.

The main published source declaration is `New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`. It says: fix a prime p, a bound s0 on the number of variables, positive rational rho, B>=0, and epsilon>0. There is H, chosen *before* the polynomials, such that any finite family of integral polynomials P_i, of arbitrary degree, with witness points x_i satisfying v(x_ij)>=rho and

\[
\sum_i v(P_i(x_i))\le B
\]

admits one tuple zeta_j of p^H-th roots of unity with v(zeta_j-1)<=rho and

\[
v(P_i(\zeta-1))\le v(P_i(x_i))+\epsilon
\]

for every i. The valuation is normalized by v(p)=1 and v(0)=infinity. The integral coefficients live in the algebraic closure of Q_p in the source theorem.

The intermediate lemma `exists_ellVal_eval_piecewise_le_add` retains an aggregate bound that the final wrapper discards: the sum of final valuations is at most B+epsilon. The stronger positive-excess form below follows directly from the one-coordinate proof.

### A quantitative H from the actual source proof

Put

\[
r_h=1/\varphi(p^h),\qquad
h_*=\min\{h\ge1:r_h\le\rho\},\qquad
\delta=\frac{\min(\epsilon,1)}{s_0+2}.
\]

Any H with

\[
B+1<\delta\sum_{h=h_*}^{H}\frac1{h+1}
\]

works. A simple explicit sufficient choice is

\[
H=\left\lceil(h_*+1)\exp((B+1)/\delta)\right\rceil.
\]

Indeed, the harmonic sum is at least `log((H+2)/(h_*+1))`, which is strictly greater than `(B+1)/delta`. This is a sufficient bound read from the source proof, not an optimality claim. The maximum order p^H is enormous (roughly double exponential in the reciprocal error allowance).

### Why the source proof works

For an integral one-variable polynomial g, write

\[
v_r(g)=\min_k(v(a_k)+kr).
\]

Roots alpha with valuation r_h contribute `#R_h r_h` to the Gauss valuation. Their total over distinct admissible h is bounded by `v_rho(g)`. A harmonic pigeonhole step finds h with few such roots in the weighted sense. Averaging distances to primitive p^h-th roots gives one zeta with `v(g(zeta-1))<=v_r_h(g)+delta`. The source declarations are `sum_card_rootsOfValuation_mul_le`, `exists_card_rootsOfValuation_mul_le`, `sum_min_ellVal_sub_le`, and `exists_rootOfUnity_eval_le_gaussVal_add`.

For many polynomials, apply this one-variable result to their product, while all other coordinates are fixed at each polynomial's own current witness. Move the coordinates one at a time. This explains both degree independence and simultaneous selection.

### Positive-excess strengthening of the finite polynomial theorem

At one coordinate step let a_i be the new value's valuation, b_i the Gauss valuation at the selected radius, and c_i the old value's valuation. The actual proof gives

\[
a_i\ge b_i,\quad c_i\ge b_i,\quad\sum_i a_i\le\sum_i b_i+\delta.
\]

All values are finite, because the right side is finite. Consequently

\[
\sum_i(a_i-c_i)_+\le\sum_i(a_i-b_i)\le\delta.
\]

For each i, the positive part of the change over several steps is bounded by the sum of its positive changes at individual steps. After s<=s0 coordinates,

\[
\boxed{\sum_i\big(v(P_i(\zeta-1))-v(P_i(x_i))\big)_+\le\epsilon.}
\]

This is a short mathematical strengthening of the source's final public wrapper; the estimates are already present in its proof. It implies both the individual and aggregate conclusions. Do not describe it as a newly discovered published theorem or as a Lean-checked extension without an independent build.

## Extension proved here: bounded power series, even infinitely many

Let C_p be the completion of the algebraic closure of Q_p, with integral ring O_Cp. Fix p, s0>=1, rational rho>0, B>=0 and epsilon>0. Choose H as above. For any 1<=s<=s0 and any index set I, possibly infinite, let

\[
F_i\in\mathcal O_{\mathbb C_p}[[T_1,\ldots,T_s]],\qquad
x_i\in\mathbb C_p^s,\qquad v(x_{ij})\ge\rho.
\]

Assume `t_i=v(F_i(x_i))<infinity` and that the total budget

\[
\sup_{J\subset I,\ J\text{ finite}}\sum_{i\in J}t_i\le B
\]

is finite. All these series converge at the stated witness points. Then one tuple zeta of p^H-th roots of unity satisfies v(zeta_j-1)<=rho and

\[
\boxed{\sup_{J\subset I,\ J\text{ finite}}
\sum_{i\in J}\big(v(F_i(\zeta-1))-t_i\big)_+\le\epsilon.}
\]

In particular every F_i(zeta-1) is nonzero,

\[
v(F_i(\zeta-1))\le t_i+\epsilon,
\quad
\sup_{J\text{ finite}}\sum_{i\in J}v(F_i(\zeta-1))\le B+\epsilon.
\]

The bound H is independent of the number of series, their degrees or coefficient complexity, and the fields needed for the coefficients and witnesses.

### Complete proof of the extension

Define the finite nonempty grid G_H of tuples whose coordinates are nontrivial p-power roots of order at most p^H with `r_H<=v(zeta_j-1)<=rho`. The lower inequality follows automatically from the order bound; the upper one discards the trivial root and the few small orders. H>=h_* ensures nonemptiness.

First fix a finite J. Choose a real M>B+epsilon+rho+1 and an integer N with `(N+1)r_H>M`. Let P_i be the total-degree N truncation of F_i. For every witness x_i and every point zeta-1 of G_H, all coordinates have valuation at least r_H. Every omitted monomial has valuation at least `(N+1)r_H>M`, because its coefficient is integral. The nonarchimedean inequality, followed by completeness, therefore gives

\[
v(F_i(y)-P_i(y))>M
\]

at every relevant point y. The strict bound can be made uniform by using the fixed lower bound `(N+1)r_H>M`.

Approximate the finitely many coefficients of these P_i by integral algebraic numbers, all to valuation precision greater than M, obtaining Q_i in O_Qpbar[T]. Approximate each coordinate of each witness x_i by an algebraic number x'_ij to valuation precision greater than M. Since M>rho, v(x'_ij)>=rho. Integral polynomials are 1-Lipschitz for the maximum p-adic norm on the unit polydisc: telescope products of integral coordinates to show that if every coordinate difference has valuation >M, so does the difference of polynomial values. Coefficient approximation also changes values by valuation >M everywhere on the unit polydisc. Thus

\[
v(Q_i(x'_i))=v(F_i(x_i))=t_i,
\]

since t_i<=B<M. Apply the strengthened finite polynomial result to the Q_i and x'_i. It gives a point zeta in G_H with the positive-excess budget <=epsilon and each v(Q_i(zeta-1))<=t_i+epsilon<=B+epsilon<M. At that grid point the difference from F_i again has valuation >M, so

\[
v(F_i(\zeta-1))=v(Q_i(\zeta-1)).
\]

This proves the statement for every finite J, with the same finite grid.

For each finite J let S_J be the subset of G_H satisfying the excess budget for J. Each S_J is nonempty. For finitely many J_1,...,J_k, the set S_(J_1 union ... union J_k) is contained in their intersection, because all excess summands are nonnegative. Hence this family has the finite intersection property. A finite set cannot have a family of subsets with the finite intersection property and empty total intersection. Any point in the total intersection gives the asserted infinite-family bound. This completes the proof.

The weaker aggregate conclusion can alternatively be proved from the source intermediate lemma without the positive-excess observation. Its finite intersection argument uses all finite partial-sum constraints `sum_J v(F_i(zeta-1))<=B+epsilon` and all pointwise constraints.

### Search of source for prior existence of this extension

No `PowerSeries.lean` occurs under `New/Congruences/Selmer`. The relevant existing file is `Lib/General/Algebra/IntegralPowerSeries.lean`, covering coefficient integrality, jets, chain rule, substitutions, exponentials and factorial valuations. It contains no torsion-selection theorem for formal power series. The RootsOfUnity theorem and its imports are independent of `New.Reduction.OneSidedBound` and `Main`: a local import-closure scan found 103 local modules, all but RootsOfUnity itself in Lib, and one external import (Mathlib). Thus this transfer does not invoke the final RH/GRH theorem.

### Why the infinite-family version should use O_Cp

Over a fixed finite K/Q_p with ramification index e, any nonunit constant coefficient has valuation at least 1/e. Thus any integral series with nonunit constant term has valuation at a witness of depth rho at least `min(rho,1/e)`. A finite total budget permits only finitely many such series; the remaining ones have unit constant term and are automatically nonzero at every point of the open unit polydisc. Allowing coefficients in O_Cp (or in algebraic extensions with unbounded ramification) makes the infinite-family statement substantive.

## Matrix and presentation corollary

Let A_i(T) be square matrices of integral bounded power series and suppose `t_i=v(det A_i(x_i))` obeys the budget above. The theorem applied to `F_i=det A_i` yields one torsion tuple at which every A_i is invertible, with

\[
\|A_i(\zeta-1)^{-1}\|_{\max}\le p^{t_i+\epsilon}.
\]

Indeed, all adjugate entries are integral, and the inverse is adj(A_i)/det(A_i). If the coefficients lie in O_K for a finite K, the matrix value lies in L=K(mu_(p^H)). Smith normal form over O_L gives

\[
v(\pi_L)\operatorname{length}_{\mathcal O_L}\operatorname{coker}A_i(\zeta-1)
=v(\det A_i(\zeta-1))\le t_i+\epsilon.
\]

For a rectangular presentation with r rows, a chosen nonzero r-by-r minor bounds the cokernel length above by the valuation of that minor. This gives a precise target for analytic presentations of Selmer groups or projection-denominator modules. It does NOT establish that a particular elliptic-curve Selmer family has such an integral presentation with the required witness/budget; those are separate arithmetic inputs.

## Two necessary-hypothesis checks

1. **Bounded integral coefficients matter.** The analytic function `log(1+T)` converges for v(T)>0 and vanishes at every p-power torsion point T=zeta-1. It has a nonzero value at T=p^2, of valuation 2, but coefficients 1/n have valuations unbounded below. No bounded denominator makes it integral. Therefore the theorem fails for arbitrary analytic functions on the open unit disk.

2. **For infinitely many constraints, separate bounds do not replace a total budget.** Let `F_h(T)=Phi_(p^h)(1+T)` for h>=1 and use the same witness T=p^2. Lifting the exponent gives `v(F_h(p^2))=1` for every h, including p=2. Every nontrivial p-power root of unity annihilates one F_h. So the separate bound t_h<=1 cannot imply a common nonvanishing torsion point. The total budget is infinite here, as it must be.

## A concrete obstruction to transplanting the packaged Selmer theorem to elliptic curves

`New/Congruences/Selmer/SelmerData.lean`, `New.Selmer.SelmerDatum`, demands:

* an inertia element gamma at a place away from p;
* its representation acts as a scalar zeta I;
* zeta^2-1 is a unit.

An unmodified rank-two p-adic Tate module of an elliptic curve cannot satisfy these assumptions. Its determinant is cyclotomic, which is trivial on inertia at places away from p. Therefore a scalar inertia action zeta I_2 has determinant zeta^2=1, so zeta^2-1=0 is not a unit. This is an elementary exact obstruction, independent of any unresolved conjecture. The same obstruction applies to Tate twists and duals, whose determinants remain unramified away from p.

A suitable preliminary finite-order character twist can change the determinant, but proving that it preserves the needed local conditions and connects back to the original Selmer problem is an additional theorem. Therefore `exists_anticyclotomic_twist` does not, as currently packaged, directly settle BSD, Goldfeld, or arbitrary elliptic-curve Selmer vanishing.

## Primary literature and research targets

1. Kriz--Nordentoft, *Horizontal p-adic L-functions*, arXiv:2310.20678. Primary full text: https://arxiv.org/html/2310.20678v2 . It already proves simultaneous nonvanishing for arbitrary finite tuples of elliptic curves under rank-zero and joint Taylor--Wiles hypotheses. Do not label simultaneous nonvanishing itself novel. The source explains that odd-order twists in positive rank require an initial nonvanishing input, supplied in many cases by Kurihara's conjecture. A torsion selector propagates finite valuation; it cannot produce the initial finite/nonzero witness from nothing.

2. Castella--Sano, *On refined nonvanishing conjectures by Kurihara and Kolyvagin*, arXiv:2601.14504. Primary: https://arxiv.org/html/2601.14504v1 and https://web.math.ucsb.edu/~castella/Kurihara.pdf . Their Theorem A equates the refined Kurihara formula with a determinantal Iwasawa Main Conjecture, under p>3, residual surjectivity and the Manin-constant condition. Theorem B proves cases of good ordinary reduction, and good supersingular reduction with squarefree conductor. This is a much sharper research target than a generic BSD claim: adapt the determinant/denominator machinery to missing local reduction cases or to uniform analytic families. The selector alone proves neither the main-conjecture determinant identity nor nonvanishing of the initial Euler-system class.

3. Serban, *An infinitesimal p-adic multiplicative Manin--Mumford conjecture*, arXiv:1607.01428, JTNB 30 (2018). Primary abstract https://arxiv.org/abs/1607.01428 . It treats rigidity and torsion zeros of integral analytic functions, including formal tori. Accordingly the broad assertion that bounded analytic functions have torsion nonvanishing is not new; any novelty claim must be restricted to the precise uniform, simultaneous, budgeted quantitative formulation, and even that priority has not been established here.

4. Fischer--Nordentoft, *Diophantine rank stability and non-vanishing of L-functions*, arXiv:2606.31646. Primary arXiv search metadata confirms a June 2026 paper proving further simultaneous nonvanishing and rank stability for modular abelian varieties of analytic rank zero, with restrictions on the finite abelian group or exceptional primes. The full text could not be opened in this subtask. Therefore use it to avoid stale claims, not for detailed unverified theorem hypotheses.

## Recommended characterization

The bounded power-series and infinite-family theorem is a rigorous extension developed in this analysis from a precise repository lemma. It is an actual mathematical output beyond RH/GRH consequences, with a complete proof and counterexamples delineating its hypotheses. It is not a demonstrated resolution of a previously named open conjecture. Its literature priority remains unestablished. The strongest research direction is simultaneous control of arithmetic determinants in p-adic families; the concrete missing work is integral presentation, a finite witness budget, and removal or redesign of the scalar-inertia restriction.
