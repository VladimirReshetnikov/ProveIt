import Surreal.HahnSeries.PolynomialSimpleRootLifting
import Surreal.HahnSeries.PolynomialFactorLifting
import Surreal.HahnSeries.PolynomialFactorUniqueness
import Surreal.HahnSeries.PronyCofactorBound
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.LinearCombination

/-!
# Residue-simple lifting and cofactor localization

This file proves `prony:lem:hensel` (the univariate clause, and the uniqueness half of the
system clause) and `prony:lem:localroots` together with `prony:eq:separation` of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`.

Throughout, `K` is any field and `Γ` any linearly ordered abelian group; the source takes
`K = ℝ` or `ℂ` and `Γ` nontrivial, and neither restriction is used. `𝒪` is the nonnegative-order
subring of `K⟦Γ⟧` (`Surreal.HahnSeries.nonnegativeSubring`), `st : 𝒪 → K` the standard part and
`𝔪` its kernel.

## Residue-simple lifting

* `existsUnique_root_of_simple_residue` (`prony:lem:hensel`, univariate clause): if `f ∈ 𝒪[Y]`,
  not necessarily monic, and its residue polynomial has a simple root `c`, then `f` has exactly
  one root `y ∈ 𝒪` with `st y = c`, that is, in `c + 𝔪`. Existence is reduced to the monic
  lifting `Surreal.HahnSeries.existsUnique_root_of_simple_standardPart` instead of the source's
  formal-parameter construction. After translating `c` to `0`, write `g = g₀ + Y q(Y)` with
  `g₀ ∈ 𝔪` and `q(0) = g₁` a unit. Then `g(g₀ s) = g₀ h(s)` with `h = 1 + Y q(g₀ Y)`, and the
  reflection `M = Y^N h(1/Y)` is monic with residue `Y^{N-1} (Y + st g₁)`. A root `r` of `M`
  with standard part `-st g₁` is a unit and `g₀ r⁻¹` is a root of `g`
  (`exists_root_of_standardPart_coeff`). Uniqueness is the source's divided-difference
  argument: `f(y') - f(y) = (y' - y)(f'(y) + k (y' - y))`, and the second factor has standard
  part `f̄'(c) ≠ 0`.
* `eq_of_isRoot_system_of_det_ne_zero` (`prony:lem:hensel`, system clause, uniqueness half): two
  solutions in `c + 𝔪^N` of a square polynomial system over `𝒪` whose residue Jacobian at `c`
  is invertible coincide. The divided-difference matrix of `exists_dividedDifference` has the
  residue Jacobian as its residue, so its determinant is nonzero.

## Cofactor localization

Let `a` be nodes, `b` cofactor coordinates and `P̂ = P + ∑ b_j Q_j`
(`Surreal.PronyBound.perturbedPoly`). The source takes `δ_i = max_{j ≠ i} v(a_i - a_j)`. Here
`δ_i ∈ Γ` is any upper bound for these valuations (hypothesis `hδ`), which already forces the
nodes to be distinct (`injective_of_le_scale`), and `v(b_i) > δ_i` for every `i` (hypothesis
`hb`). Integrality of the nodes is not used. Write `B_i = {x : v(x - a_i) > δ_i}`.

* `existsUnique_root_mem_ball`: `P̂` has exactly one root in each `B_i`. Put `τ = t^{δ_i}`,
  `s_k = τ` for `k = i` and `s_k = a_i - a_k` otherwise. Then `P̂(a_i + τ y) = (∏ s_k) F(y)` for
  the integral polynomial `F = ∏ ℓ_k + ∑_j (b_j/s_j) ∏_{k ≠ j} ℓ_k`, where
  `ℓ_k = (a_i - a_k)/s_k + (τ/s_k) Y`. Its residue `Y ∏_{k ≠ i} (1 + st(τ/(a_i - a_k)) Y)` has
  value `0` and derivative `1` at `0`, so `existsUnique_root_of_simple_residue` applies. This
  identity replaces the source's division by `Q_i`; no denominators occur.
* `not_mem_ball_of_ne`, `exists_nodes_perturbedPoly`, `isRoot_perturbedPoly_iff`,
  `separable_perturbedPoly`: the balls are disjoint, so the `n` ball roots `â_i` are distinct,
  `P̂ = ∏ (X - â_i)`, they are all the roots of `P̂`, and all are simple.
* `local_root_exact_of_mem_ball` (`prony:eq:rootexact` without the nonvanishing hypothesis of
  `Surreal.Prony.local_root_exact`), `orderTop_displacement`, `eq_node_iff` and
  `orderTop_displacement_ratio`: for a root `x ∈ B_i`, `v(x - a_i) = v(b_i)`, `x = a_i` if and
  only if `b_i = 0`, and `(x - a_i)/b_i ∈ -1 + 𝔪` when `b_i ≠ 0`.
* `orderTop_separation_ratio` (`prony:eq:separation`) and
  `orderTop_leadingCoeff_sub_of_mem_balls`: for `x ∈ B_i`, `y ∈ B_j` and `i ≠ j`,
  `(x - y)/(a_i - a_j) ∈ 1 + 𝔪`, and `x - y` has the valuation and the leading coefficient of
  `a_i - a_j`.
* `localroots` collects these statements for the ball roots `â_i`. `localroots_nearestScale`
  is the source's normalization for distinct nodes, `δ_i = max_{j ≠ i} v(a_i - a_j)`
  (`nearestScale`, with the value `0` when `n = 1`; it is defined through `HahnSeries.order`
  and so equals the source's `δ_i` only for distinct nodes).

## Pending

The existence half of the system clause of `prony:lem:hensel` (the multivariate formal
implicit-function construction of the source, evaluated strongly) is not formalized. Nothing
in `prony:lem:localroots` or `prony:eq:separation` remains pending.
-/

namespace Surreal.PronyLocal

open Polynomial Finset
open scoped _root_.HahnSeries
open Surreal.HahnSeries (nonnegativeSubring standardPart constantNonnegative
  standardPart_constantNonnegative isUnit_iff_standardPart_ne_zero)

noncomputable section

section Hensel

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- Standard part commutes with polynomial evaluation. -/
theorem standardPart_eval (p : Polynomial (nonnegativeSubring Γ K))
    (y : nonnegativeSubring Γ K) :
    standardPart Γ K (p.eval y) = (p.map (standardPart Γ K)).eval (standardPart Γ K y) := by
  rw [eval_map, eval₂_at_apply]

omit [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- Reflecting `1 + uX` in degree `m + 1` gives `X^m (X + u)`. -/
theorem reflect_one_add_X_mul_C (u : K) (m : ℕ) :
    reflect (m + 1) (1 + X * C u) = X ^ m * (X + C u) := by
  have hX : (X : K[X]) * C u = C u * X ^ 1 := by rw [pow_one, mul_comm]
  rw [reflect_add, reflect_one, hX, reflect_C_mul_X_pow, revAt_le (by omega),
    Nat.add_sub_cancel]
  ring

/-- The existence half of `prony:lem:hensel` at the residue root `0`: if the constant
coefficient is infinitesimal and the linear coefficient is a unit, the polynomial has an
infinitesimal root. No monicity is assumed. -/
theorem exists_root_of_standardPart_coeff (g : Polynomial (nonnegativeSubring Γ K))
    (h0 : standardPart Γ K (g.coeff 0) = 0) (h1 : standardPart Γ K (g.coeff 1) ≠ 0) :
    ∃ z : nonnegativeSubring Γ K, g.IsRoot z ∧ standardPart Γ K z = 0 := by
  by_cases hz : g.coeff 0 = 0
  · exact ⟨0, by rw [IsRoot.def, ← coeff_zero_eq_eval_zero, hz], map_zero _⟩
  let h : Polynomial (nonnegativeSubring Γ K) := 1 + X * g.divX.comp (C (g.coeff 0) * X)
  have hgh : ∀ s, g.eval (g.coeff 0 * s) = g.coeff 0 * h.eval s := by
    intro s
    have e := congrArg (eval (g.coeff 0 * s)) (divX_mul_X_add g)
    simp only [eval_add, eval_mul, eval_X, eval_C] at e
    simp only [h, eval_add, eval_mul, eval_X, eval_C, eval_one, eval_comp]
    rw [← e]
    ring
  have hmap : h.map (standardPart Γ K) = 1 + X * C (standardPart Γ K (g.coeff 1)) := by
    simp only [h, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul, map_X, map_comp,
      map_C, h0, C_0, zero_mul, comp_zero, ← coeff_zero_eq_eval_zero, coeff_map, coeff_divX,
      zero_add]
  have hc1 : h.coeff 1 ≠ 0 := by
    intro h'
    apply h1
    have := congrArg (fun p => p.coeff 1) hmap
    simp only [coeff_map, h', map_zero] at this
    simpa [coeff_one] using this.symm
  obtain ⟨m, hm⟩ : ∃ m, h.natDegree = m + 1 :=
    ⟨h.natDegree - 1, by have := le_natDegree_of_ne_zero hc1; omega⟩
  have hh0 : h.coeff 0 = 1 := by simp [h]
  let M := reflect (m + 1) h
  have hM : M.Monic := monic_of_natDegree_le_of_coeff_eq_one (m + 1)
    (natDegree_reflect_le.trans (by rw [hm, max_self]))
    (by rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, hh0])
  have hMmap : M.map (standardPart Γ K) =
      X ^ m * (X + C (standardPart Γ K (g.coeff 1))) := by
    rw [← reflect_map, hmap, reflect_one_add_X_mul_C]
  have hroot : (M.map (standardPart Γ K)).IsRoot (-standardPart Γ K (g.coeff 1)) := by
    rw [hMmap, IsRoot.def]
    simp
  have hder :
      (M.map (standardPart Γ K)).derivative.eval (-standardPart Γ K (g.coeff 1)) ≠ 0 := by
    rw [hMmap]
    simp only [derivative_mul, derivative_add, derivative_X, derivative_C, add_zero, eval_add,
      eval_mul, eval_pow, eval_X, eval_C, neg_add_cancel, mul_zero, zero_add, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr h1)
  obtain ⟨r, ⟨hr, hru⟩, -⟩ :=
    Surreal.HahnSeries.existsUnique_root_of_simple_standardPart M hM _ hroot hder
  have hrunit : IsUnit r :=
    (isUnit_iff_standardPart_ne_zero r).mpr (by rw [hru]; exact neg_ne_zero.mpr h1)
  let s : nonnegativeSubring Γ K := ↑hrunit.unit⁻¹
  letI : Invertible s := ⟨r, hrunit.mul_val_inv, hrunit.val_inv_mul⟩
  have hev : M.eval r * s ^ (m + 1) = h.eval s :=
    eval₂_reflect_mul_pow (RingHom.id _) s (m + 1) h hm.le
  have hs : h.eval s = 0 := by rw [← hev, hr.eq_zero, zero_mul]
  refine ⟨g.coeff 0 * s, ?_, ?_⟩
  · rw [IsRoot.def, hgh, hs, mul_zero]
  · rw [map_mul, h0, zero_mul]

/-- `prony:lem:hensel`, univariate clause: a polynomial over the nonnegative-order Hahn ring,
not necessarily monic, whose residue polynomial has a simple root `c`, has exactly one root
with standard part `c`, that is, in `c + 𝔪`. -/
theorem existsUnique_root_of_simple_residue (f : Polynomial (nonnegativeSubring Γ K)) (c : K)
    (hc : (f.map (standardPart Γ K)).IsRoot c)
    (hd : (f.map (standardPart Γ K)).derivative.eval c ≠ 0) :
    ∃! y : nonnegativeSubring Γ K, f.IsRoot y ∧ standardPart Γ K y = c := by
  have hγ : standardPart Γ K (constantNonnegative c) = c := standardPart_constantNonnegative c
  obtain ⟨z, hz, hzs⟩ := exists_root_of_standardPart_coeff (taylor (constantNonnegative c) f)
    (by rw [taylor_coeff_zero, standardPart_eval, hγ]; exact hc)
    (by rw [taylor_coeff_one, standardPart_eval, hγ, ← derivative_map]; exact hd)
  have hx : f.IsRoot (z + constantNonnegative c) := by
    rw [IsRoot.def, ← taylor_eval]
    exact hz
  have hxs : standardPart Γ K (z + constantNonnegative c) = c := by
    rw [map_add, hzs, hγ, zero_add]
  refine ⟨z + constantNonnegative c, ⟨hx, hxs⟩, ?_⟩
  rintro y ⟨hy, hys⟩
  set x := z + constantNonnegative c
  obtain ⟨k, hk⟩ := binomExpansion f x (y - x)
  have hxy : x + (y - x) = y := by ring
  rw [hxy] at hk
  have hprod : (f.derivative.eval x + k * (y - x)) * (y - x) = 0 := by
    linear_combination -hk + hy.eq_zero - hx.eq_zero
  have hT : f.derivative.eval x + k * (y - x) ≠ 0 := by
    intro h0
    have := congrArg (standardPart Γ K) h0
    rw [map_add, map_mul, map_sub, hys, hxs, sub_self, mul_zero, add_zero, standardPart_eval,
      hxs, ← derivative_map, map_zero] at this
    exact hd this
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hT))

/-- Standard part commutes with multivariate polynomial evaluation. -/
theorem standardPart_mvEval {σ : Type*} (p : MvPolynomial σ (nonnegativeSubring Γ K))
    {c : σ → K} {y : σ → nonnegativeSubring Γ K} (hyc : ∀ j, standardPart Γ K (y j) = c j) :
    standardPart Γ K (MvPolynomial.eval y p) =
      MvPolynomial.eval c (p.map (standardPart Γ K)) := by
  have hc : (standardPart Γ K) ∘ y = c := funext hyc
  change standardPart Γ K (MvPolynomial.eval₂ (RingHom.id _) y p) = _
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval_map, RingHom.comp_id, hc]

/-- Polynomial divided differences, as in the uniqueness proof of `prony:lem:hensel`:
`p(y') - p(y) = ∑_j A_j (y'_j - y_j)` with `st A_j = ∂_j p̄ (c)` when `y` and `y'` both have
standard part `c`. -/
theorem exists_dividedDifference {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ (nonnegativeSubring Γ K)) {c : σ → K}
    {y y' : σ → nonnegativeSubring Γ K} (hyc : ∀ j, standardPart Γ K (y j) = c j)
    (hy'c : ∀ j, standardPart Γ K (y' j) = c j) :
    ∃ A : σ → nonnegativeSubring Γ K,
      MvPolynomial.eval y' p - MvPolynomial.eval y p = ∑ j, A j * (y' j - y j) ∧
      ∀ j, standardPart Γ K (A j) =
        MvPolynomial.eval c (MvPolynomial.pderiv j (p.map (standardPart Γ K))) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp, fun j => by simp⟩
  | add p q hp hq =>
    obtain ⟨A, hA, hAs⟩ := hp
    obtain ⟨B, hB, hBs⟩ := hq
    refine ⟨A + B, ?_, fun j => ?_⟩
    · simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, ← hA, ← hB]
      ring
    · simp only [Pi.add_apply, map_add, hAs, hBs]
  | mul_X p k hp =>
    obtain ⟨A, hA, hAs⟩ := hp
    refine ⟨fun j => A j * y' k + if j = k then MvPolynomial.eval y p else 0, ?_, fun j => ?_⟩
    · simp only [map_mul, MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib, ite_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [show ∑ j, A j * y' k * (y' j - y j) = (∑ j, A j * (y' j - y j)) * y' k by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring, ← hA]
      ring
    · rw [map_add, map_mul, hAs, hy'c, apply_ite (standardPart Γ K), map_zero,
        standardPart_mvEval p hyc, map_mul, MvPolynomial.map_X, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X, map_add, map_mul, map_mul, MvPolynomial.eval_X, Pi.single_apply]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [hjk, Ne.symm hjk]

/-- `prony:lem:hensel`, system clause, uniqueness half: for a square polynomial system over the
nonnegative-order Hahn ring whose residue Jacobian at `c` is invertible, two solutions with
standard part `c` coincide. The existence half is not formalized here. -/
theorem eq_of_isRoot_system_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → MvPolynomial ι (nonnegativeSubring Γ K)) (c : ι → K)
    (hJ : (Matrix.of fun i j => MvPolynomial.eval c
      (MvPolynomial.pderiv j ((f i).map (standardPart Γ K)))).det ≠ 0)
    {y y' : ι → nonnegativeSubring Γ K} (hy : ∀ i, MvPolynomial.eval y (f i) = 0)
    (hy' : ∀ i, MvPolynomial.eval y' (f i) = 0) (hyc : ∀ j, standardPart Γ K (y j) = c j)
    (hy'c : ∀ j, standardPart Γ K (y' j) = c j) : y = y' := by
  choose A hA hAs using fun i => exists_dividedDifference (f i) hyc hy'c
  have hMv : Matrix.mulVec (Matrix.of A) (y' - y) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, Pi.zero_apply]
    rw [← hA i, hy i, hy' i, sub_zero]
  have hdet : (Matrix.of A).det ≠ 0 := by
    intro h0
    apply hJ
    have h := congrArg (standardPart Γ K) h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_zero] at h
    rw [← h]
    congr 1
    ext i j
    simp [hAs]
  exact (sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hdet hMv)).symm

end Hensel

section LocalRoots

open Surreal.Prony Surreal.PronyBound

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]
  {n : ℕ}

/-- Valuation of a quotient: `v(x/y) + v(y) = v(x)` for `y ≠ 0`. -/
theorem orderTop_div_add {x y : K⟦Γ⟧} (hy : y ≠ 0) :
    (x / y).orderTop + y.orderTop = x.orderTop := by
  rw [← _root_.HahnSeries.orderTop_mul, div_mul_cancel₀ x hy]

/-- A quotient is integral when the denominator has no larger valuation. -/
theorem orderTop_div_nonneg {x y : K⟦Γ⟧} (hy : y ≠ 0) (h : y.orderTop ≤ x.orderTop) :
    0 ≤ (x / y).orderTop := by
  rwa [← WithTop.add_le_add_iff_right (_root_.HahnSeries.orderTop_ne_top.mpr hy), zero_add,
    orderTop_div_add hy]

/-- A quotient is infinitesimal when the denominator has smaller valuation. -/
theorem orderTop_div_pos {x y : K⟦Γ⟧} (hy : y ≠ 0) (h : y.orderTop < x.orderTop) :
    0 < (x / y).orderTop := by
  rwa [← WithTop.add_lt_add_iff_right (_root_.HahnSeries.orderTop_ne_top.mpr hy), zero_add,
    orderTop_div_add hy]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The valuation of a difference is symmetric. -/
theorem orderTop_sub_comm (x y : K⟦Γ⟧) : (x - y).orderTop = (y - x).orderTop := by
  rw [← neg_sub, _root_.HahnSeries.orderTop_neg]

variable {a b : Fin n → K⟦Γ⟧} {δ : Fin n → Γ}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- Finite nearest-neighbour scales force the nodes to be distinct. -/
theorem injective_of_le_scale (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  have h := hδ j i hne
  rw [hij, sub_self, _root_.HahnSeries.orderTop_zero] at h
  exact absurd h (not_le.mpr (WithTop.coe_lt_top _))

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- A node `a_j`, `j ≠ i`, does not lie in the strict ball `B_i`. -/
theorem ne_of_mem_ball (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) {i j : Fin n}
    (hji : j ≠ i) {x : K⟦Γ⟧} (hx : (δ i : WithTop Γ) < (x - a i).orderTop) : x ≠ a j := by
  rintro rfl
  exact absurd hx (not_lt.mpr (by rw [orderTop_sub_comm]; exact hδ i j hji))

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The strict balls `B_i = {x : v(x - a_i) > δ_i}` are pairwise disjoint. -/
theorem not_mem_ball_of_ne (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) {i j : Fin n}
    (hij : i ≠ j) {x : K⟦Γ⟧} (hi : (δ i : WithTop Γ) < (x - a i).orderTop)
    (hj : (δ j : WithTop Γ) < (x - a j).orderTop) : False := by
  have h1 : (a i - a j).orderTop < (x - a i).orderTop := (hδ i j (Ne.symm hij)).trans_lt hi
  have h2 : (a i - a j).orderTop < (x - a j).orderTop := by
    rw [orderTop_sub_comm]
    exact (hδ j i hij).trans_lt hj
  have h3 : min (x - a j).orderTop (x - a i).orderTop ≤ (a i - a j).orderTop := by
    have := _root_.HahnSeries.min_orderTop_le_orderTop_sub (x := x - a j) (y := x - a i)
    rwa [sub_sub_sub_cancel_left] at this
  exact absurd h3 (not_le.mpr (lt_min h2 h1))

/-- `prony:lem:localroots`, local existence and uniqueness: the perturbation
`P̂ = P + ∑ b_j Q_j` has exactly one root in the strict ball
`B_i = {x : v(x - a_i) > δ_i}`. Here `δ_i` is any upper bound for the valuations
`v(a_i - a_j)`, `j ≠ i`, and `v(b_j) > δ_j` for every `j`. -/
theorem existsUnique_root_mem_ball (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) (i : Fin n) :
    ∃! x : K⟦Γ⟧, (δ i : WithTop Γ) < (x - a i).orderTop ∧ (perturbedPoly a b).IsRoot x := by
  set τ : K⟦Γ⟧ := _root_.HahnSeries.single (δ i) 1
  have hτv : τ.orderTop = δ i := _root_.HahnSeries.orderTop_single one_ne_zero
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, _root_.HahnSeries.orderTop_zero] at hτv
    exact WithTop.top_ne_coe hτv
  let s : Fin n → K⟦Γ⟧ := fun k => if k = i then τ else a i - a k
  have hs0 : ∀ k, s k ≠ 0 := by
    intro k
    by_cases hk : k = i
    · simp only [s, if_pos hk]
      exact hτ0
    · simp only [s, if_neg hk]
      exact sub_ne_zero.mpr ((injective_of_le_scale hδ).ne (Ne.symm hk))
  have hsa : ∀ k, (s k).orderTop ≤ (a i - a k).orderTop := by
    intro k
    by_cases hk : k = i
    · simp only [s, hk, sub_self, _root_.HahnSeries.orderTop_zero, le_top]
    · simp only [s, if_neg hk, le_refl]
  have hsδ : ∀ k, (s k).orderTop ≤ δ i := by
    intro k
    by_cases hk : k = i
    · simp only [s, if_pos hk, hτv, le_refl]
    · simp only [s, if_neg hk]
      exact hδ i k hk
  have hsb : ∀ k, (s k).orderTop < (b k).orderTop := by
    intro k
    by_cases hk : k = i
    · simp only [s, if_pos hk, hτv]
      rw [hk]
      exact hb i
    · simp only [s, if_neg hk]
      rw [orderTop_sub_comm]
      exact (hδ k i (Ne.symm hk)).trans_lt (hb k)
  let e : Fin n → nonnegativeSubring Γ K := fun k =>
    ⟨(a i - a k) / s k, orderTop_div_nonneg (hs0 k) (hsa k)⟩
  let α : Fin n → nonnegativeSubring Γ K := fun k =>
    ⟨τ / s k, orderTop_div_nonneg (hs0 k) (by rw [hτv]; exact hsδ k)⟩
  let γ : Fin n → nonnegativeSubring Γ K := fun k =>
    ⟨b k / s k, (orderTop_div_pos (hs0 k) (hsb k)).le⟩
  let ℓ : Fin n → Polynomial (nonnegativeSubring Γ K) := fun k => C (e k) + C (α k) * X
  let F : Polynomial (nonnegativeSubring Γ K) :=
    ∏ k, ℓ k + ∑ j, C (γ j) * ∏ k ∈ univ.erase j, ℓ k
  -- The scaled equation: `P̂(a_i + τ y) = (∏ s_k) F(y)`.
  have hFeval : ∀ y : nonnegativeSubring Γ K,
      (∏ k, s k) * ((F.eval y : nonnegativeSubring Γ K) : K⟦Γ⟧) =
        (perturbedPoly a b).eval (a i + τ * y) := by
    intro y
    have hℓ : ∀ k, (((ℓ k).eval y : nonnegativeSubring Γ K) : K⟦Γ⟧) =
        (a i - a k) / s k + τ / s k * y := by
      intro k
      simp only [ℓ, eval_add, eval_C, eval_mul, eval_X]
      rfl
    have hL : ∀ k, a i + τ * y - a k =
        s k * (((ℓ k).eval y : nonnegativeSubring Γ K) : K⟦Γ⟧) := by
      intro k
      rw [hℓ k]
      have h1 : s k * ((a i - a k) / s k) = a i - a k := mul_div_cancel₀ _ (hs0 k)
      have h2 : s k * (τ / s k) = τ := mul_div_cancel₀ _ (hs0 k)
      linear_combination (-1 : K⟦Γ⟧) * h1 - (y : K⟦Γ⟧) * h2
    have hF : ((F.eval y : nonnegativeSubring Γ K) : K⟦Γ⟧) =
        ∏ k, (((ℓ k).eval y : nonnegativeSubring Γ K) : K⟦Γ⟧) +
          ∑ j, b j / s j * ∏ k ∈ univ.erase j,
            (((ℓ k).eval y : nonnegativeSubring Γ K) : K⟦Γ⟧) := by
      simp only [F, eval_add, eval_prod, eval_finsetSum, eval_mul, eval_C, Subring.coe_add,
        Subring.coe_mul, SubmonoidClass.coe_finsetProd, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [hF, mul_add, Finset.mul_sum, ← prod_mul_distrib]
    simp only [perturbedPoly, nodePoly, cofactor, eval_add, eval_prod, eval_finsetSum,
      eval_mul, eval_C, eval_sub, eval_X, hL]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [prod_mul_distrib, ← mul_prod_erase univ s (mem_univ j)]
    have h3 : s j * (b j / s j) = b j := mul_div_cancel₀ _ (hs0 j)
    linear_combination (∏ k ∈ univ.erase j, s k) *
      (∏ k ∈ univ.erase j, (((ℓ k).eval y : nonnegativeSubring Γ K) : K⟦Γ⟧)) * h3
  -- The residue polynomial of `F` has the simple root `0`.
  have he_i : e i = 0 := Subtype.ext (by simp [e, s])
  have hα_i : α i = 1 := Subtype.ext (by simp [α, s, hτ0])
  have he_k : ∀ k ∈ univ.erase i, e k = 1 := by
    intro k hk
    have hne : a i - a k ≠ 0 :=
      sub_ne_zero.mpr ((injective_of_le_scale hδ).ne (ne_of_mem_erase hk).symm)
    exact Subtype.ext (by simp [e, s, ne_of_mem_erase hk, hne])
  have hγ : ∀ k, standardPart Γ K (γ k) = 0 := fun k =>
    _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop (orderTop_div_pos (hs0 k) (hsb k))
  have hres0 : (F.map (standardPart Γ K)).IsRoot 0 := by
    have h := standardPart_eval F 0
    rw [map_zero] at h
    rw [IsRoot.def, ← h]
    simp only [F, ℓ, eval_add, eval_prod, eval_finsetSum, eval_mul, eval_C, eval_X, mul_zero,
      add_zero, map_add, map_prod, map_sum, map_mul, hγ, zero_mul, sum_const_zero]
    exact prod_eq_zero (mem_univ i) (by rw [he_i, map_zero])
  have hres1 : (F.map (standardPart Γ K)).derivative.eval 0 ≠ 0 := by
    have h := standardPart_eval (derivative F) 0
    rw [map_zero] at h
    rw [derivative_map, ← h]
    have hℓi : ℓ i = X := by simp [ℓ, he_i, hα_i]
    have hsplit : ∏ k, ℓ k = X * ∏ k ∈ univ.erase i, ℓ k := by
      rw [← hℓi, mul_prod_erase univ ℓ (mem_univ i)]
    simp only [F, hsplit, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
      one_mul, eval_add, eval_finsetSum, eval_mul, eval_C, eval_X, map_add, map_sum, map_mul, hγ,
      sum_const_zero, add_zero]
    rw [eval_prod, map_prod, prod_eq_one]
    · exact one_ne_zero
    intro k hk
    simp [ℓ, he_k k hk]
  obtain ⟨y₀, ⟨hy₀, hy₀s⟩, huniq⟩ := existsUnique_root_of_simple_residue F 0 hres0 hres1
  have hy₀v : 0 < (y₀ : K⟦Γ⟧).orderTop :=
    (Surreal.HahnSeries.coeff_zero_eq_zero_iff_orderTop_pos _
      ((Surreal.HahnSeries.mem_nonnegativeSubring _).mp y₀.2)).mp hy₀s
  refine ⟨a i + τ * y₀, ⟨?_, ?_⟩, ?_⟩
  · rw [add_sub_cancel_left, _root_.HahnSeries.orderTop_mul, hτv]
    calc (δ i : WithTop Γ) = δ i + 0 := (add_zero _).symm
      _ < δ i + (y₀ : K⟦Γ⟧).orderTop := WithTop.add_lt_add_left WithTop.coe_ne_top hy₀v
  · rw [IsRoot.def, ← hFeval, hy₀.eq_zero]
    simp
  · rintro x ⟨hx, hxr⟩
    have hy : 0 < ((x - a i) / τ).orderTop := orderTop_div_pos hτ0 (by rw [hτv]; exact hx)
    let y : nonnegativeSubring Γ K := ⟨(x - a i) / τ, hy.le⟩
    have hxy : a i + τ * (y : K⟦Γ⟧) = x := by
      change a i + τ * ((x - a i) / τ) = x
      rw [mul_div_cancel₀ _ hτ0]
      ring
    have hFy : F.IsRoot y := by
      have h := hFeval y
      rw [hxy, hxr.eq_zero] at h
      exact Subtype.ext ((mul_eq_zero.mp h).resolve_left (prod_ne_zero_iff.mpr fun k _ => hs0 k))
    have hys : standardPart Γ K y = 0 := _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop hy
    rw [← hxy, huniq y ⟨hFy, hys⟩]

/-- `prony:lem:localroots`, global part: the roots `â_i` in the balls `B_i` are distinct and
are all the roots of `P̂`, all simple, because `P̂ = ∏ (X - â_i)`. -/
theorem exists_nodes_perturbedPoly (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) :
    ∃ â : Fin n → K⟦Γ⟧, Function.Injective â ∧
      (∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop) ∧ perturbedPoly a b = nodePoly â := by
  choose â hâ using fun i => (existsUnique_root_mem_ball hδ hb i).exists
  have hinj : Function.Injective â := by
    intro i j hij
    by_contra hne
    exact not_mem_ball_of_ne hδ hne (hâ i).1 (by rw [hij]; exact (hâ j).1)
  refine ⟨â, hinj, fun i => (hâ i).1, ?_⟩
  refine eq_of_monic_of_dvd_of_natDegree_le (nodePoly_monic â) (perturbedPoly_monic a b) ?_
    (by rw [natDegree_perturbedPoly, natDegree_nodePoly])
  change ∏ i, (X - C (â i)) ∣ _
  exact Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _)
    fun i _ => dvd_iff_isRoot.mpr (hâ i).2

/-- The bracket `∑_{j ≠ i} b_j / (x - a_j)` of `prony:eq:rootexact` is infinitesimal at every
point of the ball `B_i`. -/
theorem orderTop_bracket_pos (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) {i : Fin n} {x : K⟦Γ⟧}
    (hx : (δ i : WithTop Γ) < (x - a i).orderTop) :
    0 < (∑ j ∈ univ.erase i, b j / (x - a j)).orderTop := by
  refine lt_orderTop_sum (by simp) fun j hj => ?_
  have hji : j ≠ i := ne_of_mem_erase hj
  have hxj : x - a j ≠ 0 := sub_ne_zero.mpr (ne_of_mem_ball hδ hji hx)
  refine orderTop_div_pos hxj ?_
  have h1 : (a i - a j).orderTop < (x - a i).orderTop := (hδ i j hji).trans_lt hx
  have h2 : (x - a j).orderTop = (a i - a j).orderTop := by
    have : x - a j = (x - a i) + (a i - a j) := by ring
    rw [this, _root_.HahnSeries.orderTop_add_eq_right h1]
  rw [h2, orderTop_sub_comm]
  exact (hδ j i (Ne.symm hji)).trans_lt (hb j)

/-- The bracket `1 + ∑_{j ≠ i} b_j / (x - a_j)` has valuation zero on `B_i`. -/
theorem orderTop_one_add_bracket (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) {i : Fin n} {x : K⟦Γ⟧}
    (hx : (δ i : WithTop Γ) < (x - a i).orderTop) :
    (1 + ∑ j ∈ univ.erase i, b j / (x - a j)).orderTop = 0 := by
  rw [_root_.HahnSeries.orderTop_add_eq_left, _root_.HahnSeries.orderTop_one]
  rw [_root_.HahnSeries.orderTop_one]
  exact orderTop_bracket_pos hδ hb hx

/-- `prony:eq:rootexact` on the ball `B_i`, where the bracket is automatically nonzero:
`z_i = -b_i (1 + ∑_{j ≠ i} b_j/(a_i - a_j + z_i))⁻¹`. -/
theorem local_root_exact_of_mem_ball (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) {i : Fin n} {x : K⟦Γ⟧}
    (hx : (δ i : WithTop Γ) < (x - a i).orderTop) (hr : (perturbedPoly a b).IsRoot x) :
    x - a i = -b i * (1 + ∑ j ∈ univ.erase i, b j / (x - a j))⁻¹ := by
  refine local_root_exact a b (fun j hji => ne_of_mem_ball hδ hji hx) hr ?_
  intro h0
  have h := orderTop_one_add_bracket hδ hb hx
  rw [h0, _root_.HahnSeries.orderTop_zero] at h
  exact WithTop.top_ne_coe h

/-- `prony:lem:localroots`: a root `x` of `P̂` in `B_i` has displacement valuation
`v(x - a_i) = v(b_i)`. -/
theorem orderTop_displacement (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) {i : Fin n} {x : K⟦Γ⟧}
    (hx : (δ i : WithTop Γ) < (x - a i).orderTop) (hr : (perturbedPoly a b).IsRoot x) :
    (x - a i).orderTop = (b i).orderTop := by
  have hm := local_root_mul a b (fun j hji => ne_of_mem_ball hδ hji hx) hr
  have h := congrArg _root_.HahnSeries.orderTop hm
  rwa [_root_.HahnSeries.orderTop_mul, orderTop_one_add_bracket hδ hb hx, add_zero,
    _root_.HahnSeries.orderTop_neg] at h

/-- `prony:lem:localroots`: the displacement vanishes exactly when `b_i = 0`. -/
theorem eq_node_iff (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) {i : Fin n} {x : K⟦Γ⟧}
    (hx : (δ i : WithTop Γ) < (x - a i).orderTop) (hr : (perturbedPoly a b).IsRoot x) :
    x = a i ↔ b i = 0 := by
  rw [← sub_eq_zero, ← _root_.HahnSeries.orderTop_eq_top, orderTop_displacement hδ hb hx hr,
    _root_.HahnSeries.orderTop_eq_top]

/-- `prony:lem:localroots`: for `b_i ≠ 0`, the ratio `z_i / b_i` lies in `-1 + 𝔪`. -/
theorem orderTop_displacement_ratio (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) {i : Fin n} {x : K⟦Γ⟧}
    (hx : (δ i : WithTop Γ) < (x - a i).orderTop) (hr : (perturbedPoly a b).IsRoot x)
    (hbi : b i ≠ 0) : 0 < ((x - a i) / b i + 1).orderTop := by
  have hS := orderTop_bracket_pos hδ hb hx
  have hm := local_root_mul a b (fun j hji => ne_of_mem_ball hδ hji hx) hr
  have hkey : ((x - a i) / b i + 1) * b i =
      -((x - a i) * ∑ j ∈ univ.erase i, b j / (x - a j)) := by
    rw [add_mul, div_mul_cancel₀ _ hbi, one_mul]
    linear_combination hm
  have hv := congrArg _root_.HahnSeries.orderTop hkey
  rw [_root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_neg,
    _root_.HahnSeries.orderTop_mul, orderTop_displacement hδ hb hx hr] at hv
  have hbt : (b i).orderTop ≠ ⊤ := _root_.HahnSeries.orderTop_ne_top.mpr hbi
  have h := WithTop.add_lt_add_left hbt hS
  rw [add_zero, ← hv] at h
  exact (WithTop.add_lt_add_iff_right hbt).mp (by rwa [zero_add])

/-- `prony:eq:separation`, for arbitrary points of two different balls:
`(x - y)/(a_i - a_j) ∈ 1 + 𝔪` whenever `x ∈ B_i`, `y ∈ B_j` and `i ≠ j`. -/
theorem orderTop_separation_ratio (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {i j : Fin n} (hij : i ≠ j) {x y : K⟦Γ⟧} (hx : (δ i : WithTop Γ) < (x - a i).orderTop)
    (hy : (δ j : WithTop Γ) < (y - a j).orderTop) :
    0 < ((x - y) / (a i - a j) - 1).orderTop := by
  have hD : a i - a j ≠ 0 := sub_ne_zero.mpr ((injective_of_le_scale hδ).ne hij)
  rw [div_sub_one hD]
  refine orderTop_div_pos hD ?_
  have h1 : (a i - a j).orderTop < (x - a i).orderTop := (hδ i j (Ne.symm hij)).trans_lt hx
  have h2 : (a i - a j).orderTop < (y - a j).orderTop := by
    rw [orderTop_sub_comm]
    exact (hδ j i hij).trans_lt hy
  have : x - y - (a i - a j) = (x - a i) - (y - a j) := by ring
  rw [this]
  exact (lt_min h1 h2).trans_le _root_.HahnSeries.min_orderTop_le_orderTop_sub

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The consequence stated after `prony:eq:separation`: the valuation and the leading
coefficient of a node difference are unchanged when the nodes move inside their balls. -/
theorem orderTop_leadingCoeff_sub_of_mem_balls
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) {i j : Fin n} (hij : i ≠ j)
    {x y : K⟦Γ⟧} (hx : (δ i : WithTop Γ) < (x - a i).orderTop)
    (hy : (δ j : WithTop Γ) < (y - a j).orderTop) :
    (x - y).orderTop = (a i - a j).orderTop ∧
      (x - y).leadingCoeff = (a i - a j).leadingCoeff := by
  have h1 : (a i - a j).orderTop < (x - a i).orderTop := (hδ i j (Ne.symm hij)).trans_lt hx
  have h2 : (a i - a j).orderTop < (y - a j).orderTop := by
    rw [orderTop_sub_comm]
    exact (hδ j i hij).trans_lt hy
  have h3 : (a i - a j).orderTop < ((x - a i) - (y - a j)).orderTop :=
    (lt_min h1 h2).trans_le _root_.HahnSeries.min_orderTop_le_orderTop_sub
  have he : x - y = (a i - a j) + ((x - a i) - (y - a j)) := by abel
  rw [he]
  exact ⟨_root_.HahnSeries.orderTop_add_eq_left h3,
    _root_.HahnSeries.leadingCoeff_add_eq_left h3⟩

/-- `prony:lem:localroots` together with `prony:eq:separation`. Let `δ_i` bound the valuations
`v(a_i - a_j)`, `j ≠ i`, from above (which forces distinct nodes) and let `v(b_i) > δ_i`.
Then there are distinct `â_i` with `P̂ = ∏ (X - â_i)`, each `â_i` is the unique root of `P̂` in
`B_i`, `v(â_i - a_i) = v(b_i)`, `â_i = a_i ↔ b_i = 0`, `(â_i - a_i)/b_i ∈ -1 + 𝔪` for
`b_i ≠ 0`, and `(â_i - â_j)/(a_i - a_j) ∈ 1 + 𝔪` for `i ≠ j`. -/
theorem localroots (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) :
    ∃ â : Fin n → K⟦Γ⟧, Function.Injective â ∧ perturbedPoly a b = nodePoly â ∧
      (∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop) ∧
      (∀ i x, (δ i : WithTop Γ) < (x - a i).orderTop → (perturbedPoly a b).IsRoot x →
        x = â i) ∧
      (∀ i, (â i - a i).orderTop = (b i).orderTop) ∧
      (∀ i, â i = a i ↔ b i = 0) ∧
      (∀ i, b i ≠ 0 → 0 < ((â i - a i) / b i + 1).orderTop) ∧
      (∀ i j, i ≠ j → 0 < ((â i - â j) / (a i - a j) - 1).orderTop) := by
  obtain ⟨â, hinj, hball, hP⟩ := exists_nodes_perturbedPoly hδ hb
  have hroot : ∀ i, (perturbedPoly a b).IsRoot (â i) := fun i => by
    rw [hP, IsRoot.def, eval_nodePoly_eq_zero_iff]
    exact ⟨i, rfl⟩
  refine ⟨â, hinj, hP, hball, fun i x hx hr => ?_, fun i => ?_, fun i => ?_, fun i hbi => ?_,
    fun i j hij => ?_⟩
  · exact (existsUnique_root_mem_ball hδ hb i).unique ⟨hx, hr⟩ ⟨hball i, hroot i⟩
  · exact orderTop_displacement hδ hb (hball i) (hroot i)
  · exact eq_node_iff hδ hb (hball i) (hroot i)
  · exact orderTop_displacement_ratio hδ hb (hball i) (hroot i) hbi
  · exact orderTop_separation_ratio hδ hij (hball i) (hball j)

/-- "These are all its roots": the roots of `P̂` are exactly the ball roots `â_i`. -/
theorem isRoot_perturbedPoly_iff {â : Fin n → K⟦Γ⟧} (hP : perturbedPoly a b = nodePoly â)
    (x : K⟦Γ⟧) : (perturbedPoly a b).IsRoot x ↔ x ∈ Set.range â := by
  rw [hP, IsRoot.def, eval_nodePoly_eq_zero_iff]

/-- "They are simple": under the hypotheses of `prony:lem:localroots`, `P̂` is separable. -/
theorem separable_perturbedPoly (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i).orderTop) : (perturbedPoly a b).Separable := by
  obtain ⟨â, hinj, -, hP⟩ := exists_nodes_perturbedPoly hδ hb
  rw [hP]
  exact separable_prod_X_sub_C_iff.mpr hinj

/-- The nearest-neighbour scale `δ_i = max_{j ≠ i} v(a_i - a_j)` of `prony:eq:geometry`, with
the source's convention `δ_i = 0` when there is no other node. It is built from
`HahnSeries.order`, which is `0` (not `⊤`) on the zero series, so it agrees with the source's
`δ_i` for distinct nodes (the source's standing assumption); a node coinciding with `a_i`
contributes `0` to the maximum instead of `⊤`. -/
def nearestScale (a : Fin n → K⟦Γ⟧) (i : Fin n) : Γ :=
  if h : (univ.erase i).Nonempty then (univ.erase i).sup' h fun j => (a i - a j).order else 0

omit [IsOrderedAddMonoid Γ] in
/-- For distinct nodes, `nearestScale` bounds every `v(a_i - a_j)`, `j ≠ i`. -/
theorem orderTop_sub_le_nearestScale (ha : Function.Injective a) (i j : Fin n) (hji : j ≠ i) :
    (a i - a j).orderTop ≤ (nearestScale a i : Γ) := by
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨hji, mem_univ j⟩
  rw [nearestScale, dif_pos ⟨j, hj⟩, ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero
    (sub_ne_zero.mpr (ha.ne (Ne.symm hji)))]
  exact WithTop.coe_le_coe.mpr (le_sup' (fun j => (a i - a j).order) hj)

omit [IsOrderedAddMonoid Γ] in
/-- For distinct nodes and at least one other node, the maximum defining `nearestScale` is
attained: some `j ≠ i` has `v(a_i - a_j) = δ_i`. -/
theorem exists_orderTop_sub_eq_nearestScale (ha : Function.Injective a) (i : Fin n)
    (h : (univ.erase i).Nonempty) :
    ∃ j, j ≠ i ∧ (a i - a j).orderTop = (nearestScale a i : Γ) := by
  obtain ⟨j, hj, hjeq⟩ := (univ.erase i).exists_mem_eq_sup' h fun j => (a i - a j).order
  have hji : j ≠ i := ne_of_mem_erase hj
  refine ⟨j, hji, ?_⟩
  rw [nearestScale, dif_pos h, hjeq, ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero
    (sub_ne_zero.mpr (ha.ne (Ne.symm hji)))]

omit [IsOrderedAddMonoid Γ] in
/-- With no other node, `nearestScale a i = 0`: the source's convention for `n = 1`. -/
theorem nearestScale_of_not_nonempty {i : Fin n} (h : ¬(univ.erase i).Nonempty) :
    nearestScale a i = 0 :=
  dif_neg h

/-- `prony:lem:localroots` in the source's normalization: distinct nodes, the nearest-neighbour
scales `δ_i = max_{j ≠ i} v(a_i - a_j)` and `v(b_i) > δ_i` for every `i`. -/
theorem localroots_nearestScale (ha : Function.Injective a)
    (hb : ∀ i, ((nearestScale a i : Γ) : WithTop Γ) < (b i).orderTop) :
    ∃ â : Fin n → K⟦Γ⟧, Function.Injective â ∧ perturbedPoly a b = nodePoly â ∧
      (∀ i, ((nearestScale a i : Γ) : WithTop Γ) < (â i - a i).orderTop) ∧
      (∀ i x, ((nearestScale a i : Γ) : WithTop Γ) < (x - a i).orderTop →
        (perturbedPoly a b).IsRoot x → x = â i) ∧
      (∀ i, (â i - a i).orderTop = (b i).orderTop) ∧
      (∀ i, â i = a i ↔ b i = 0) ∧
      (∀ i, b i ≠ 0 → 0 < ((â i - a i) / b i + 1).orderTop) ∧
      (∀ i j, i ≠ j → 0 < ((â i - â j) / (a i - a j) - 1).orderTop) :=
  localroots (orderTop_sub_le_nearestScale ha) hb

end LocalRoots

end

end Surreal.PronyLocal
