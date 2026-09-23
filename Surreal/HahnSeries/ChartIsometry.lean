import Surreal.HahnSeries.MvEvaluation
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Valuation isometry for formal charts

This file proves `tate:node:lem:isometry` in
`docs/surcomplex/hahn-tate-uniformization/article.tex`.

For a finite vector `a = (a_1, …, a_d)` of Hahn series put `𝐯(a) = min_j v(a_j)`, with
`v(0) = ∞`; this is `vecOrderTop`. Let `A = (A_1, …, A_d)` be formal power series in
`Z_1, …, Z_d` whose linear part `L_A` (the matrix of coefficients of the `Z_j`) is invertible.
Evaluating `A` strongly at vectors `a, b` of positive-order Hahn series, we prove
`𝐯(A(a) - A(b)) = 𝐯(a - b)` (`vecOrderTop_mvEvaluate_sub`); the case `a = b` is included.

The proof follows the source. Split `A_i` into its constant term, its linear part
`∑_j (L_A)_{ij} Z_j` and a remainder `nonlinearPart A i` whose coefficients vanish in total
degree at most one. Every substituted monomial of degree `n ≥ 1` satisfies
`v(a^e - b^e) ≥ 𝐯(a - b) + (n - 1) ε`, where `ε > 0` is the least order among the coordinates
of `a` and `b`; so the nonlinear difference has order at least `𝐯(a - b) + ε`. An invertible
constant matrix preserves `𝐯`, and the nonlinear term cannot cancel a coordinate of least
valuation. Instead of the formal factorization `N(a) - N(b) = C(a, b)(a - b)` of the source we
bound the strong sum term by term, which avoids evaluating in `2d` variables.

The statement is proved more generally than in the source:
* the coefficients lie in any commutative ring `R` (the source takes a field `k` of
  characteristic zero), and invertibility of `L_A` means `IsUnit L_A` in the matrix ring;
* the exponent monoid `Γ` is any linearly ordered cancellative commutative monoid (the source
  takes an ordered abelian group), and the index type of the variables is any finite type;
* no zero-constant-term hypothesis on `A` is needed, since constant terms cancel in `A(a) - A(b)`
  (the source assumes it so that `A` maps `m_v^d` to itself).

`isometry_of_det_ne_zero` restates the result in the source's setting: a field `k`, an ordered
abelian group `Γ`, `d` variables and `det L_A ≠ 0`.

Nothing of the lemma remains pending. The consequence `tate:node:cor:bidisk` for the node chart
is not formalized here; its bijectivity also needs `tate:node:lem:implicit`.
-/

namespace Surreal.ChartIsometry

open _root_.HahnSeries Surreal.HahnSeries

noncomputable section

variable {Γ R σ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R]

/-! ### Order bounds for finite and strong sums -/

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Ultrametric lower bound for a finite sum of Hahn series. -/
theorem le_orderTop_finset_sum {ι : Type*} (s : Finset ι) (f : ι → R⟦Γ⟧) {g : WithTop Γ}
    (h : ∀ i ∈ s, g ≤ (f i).orderTop) : g ≤ (∑ i ∈ s, f i).orderTop :=
  Finset.sum_induction f (fun x => g ≤ x.orderTop)
    (fun _ _ hx hy => (le_min hx hy).trans min_orderTop_le_orderTop_add) (by simp) h

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- A uniform lower bound on the orders of the terms of a strongly summable family bounds the
order of its strong sum. -/
theorem le_orderTop_hsum {ι : Type*} (s : SummableFamily Γ R ι) {g : WithTop Γ}
    (h : ∀ i, g ≤ (s i).orderTop) : g ≤ s.hsum.orderTop := by
  refine le_orderTop_iff_forall.mpr fun j hj => ?_
  rw [SummableFamily.coeff_hsum]
  exact finsum_eq_zero_of_forall_eq_zero fun i =>
    coeff_eq_zero_of_lt_orderTop (hj.trans_le (h i))

/-! ### Differences of substituted monomials -/

omit [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] in
theorem prod_pow_eq_prod_map_toMultiset [Fintype σ] {M : Type*} [CommMonoid M] (x : σ → M)
    (e : σ →₀ ℕ) : ∏ i, x i ^ e i = (e.toMultiset.map x).prod := by
  classical
  rw [Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset]
  refine (Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

/-- A product of `n` factors of order at least `ε` has order at least `n • ε`. -/
theorem card_nsmul_le_orderTop_prod_map (x : σ → R⟦Γ⟧) {ε : WithTop Γ}
    (hx : ∀ j, ε ≤ (x j).orderTop) (m : Multiset σ) :
    Multiset.card m • ε ≤ (m.map x).prod.orderTop := by
  induction m using Multiset.induction_on with
  | empty => simpa using orderTop_nsmul_le_orderTop_pow (x := (1 : R⟦Γ⟧)) (n := 0)
  | cons j m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul']
    exact (add_le_add (hx j) ih).trans orderTop_add_le_mul

private theorem add_nsmul_le_add (ρ : WithTop Γ) {ε : WithTop Γ} (hε : 0 ≤ ε) (n : ℕ) :
    ρ + n • ε ≤ ε + (ρ + (n - 1) • ε) := by
  cases n with
  | zero => simpa using le_add_of_nonneg_left hε
  | succ n => rw [succ_nsmul', Nat.add_sub_cancel, add_left_comm]

/-- A difference of two products of `n` factors gains one factor `ε` per extra factor:
`v(∏ a_j - ∏ b_j) ≥ ρ + (n - 1) ε` when every `a_j - b_j` has order at least `ρ` and every
`a_j, b_j` has order at least `ε ≥ 0`. -/
theorem add_le_orderTop_prod_map_sub (a b : σ → R⟦Γ⟧) {ρ ε : WithTop Γ} (hε : 0 ≤ ε)
    (ha : ∀ j, ε ≤ (a j).orderTop) (hb : ∀ j, ε ≤ (b j).orderTop)
    (hab : ∀ j, ρ ≤ (a j - b j).orderTop) (m : Multiset σ) :
    ρ + (Multiset.card m - 1) • ε ≤ ((m.map a).prod - (m.map b).prod).orderTop := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons j m ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
      Multiset.card_cons, Nat.add_sub_cancel]
    have key : a j * (m.map a).prod - b j * (m.map b).prod =
        a j * ((m.map a).prod - (m.map b).prod) + (a j - b j) * (m.map b).prod := by ring
    rw [key]
    refine le_trans (le_min ?_ ?_) min_orderTop_le_orderTop_add
    · exact (add_nsmul_le_add ρ hε _).trans ((add_le_add (ha j) ih).trans orderTop_add_le_mul)
    · exact (add_le_add (hab j) (card_nsmul_le_orderTop_prod_map b hb m)).trans
        orderTop_add_le_mul

omit [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] in
/-- An exponent vector that is neither zero nor a single variable has total degree at least
two. -/
theorem two_le_card_toMultiset {e : σ →₀ ℕ} (h0 : e ≠ 0)
    (h1 : ∀ j, e ≠ Finsupp.single j 1) : 2 ≤ Multiset.card e.toMultiset := by
  classical
  rcases Nat.lt_or_ge (Multiset.card e.toMultiset) 2 with hlt | hge
  · exfalso
    obtain h | h : Multiset.card e.toMultiset = 0 ∨ Multiset.card e.toMultiset = 1 := by omega
    · exact h0 ((Finsupp.toMultiset_eq_iff.mp (Multiset.card_eq_zero.mp h)).trans
        Multiset.toFinsupp_zero)
    · obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp h
      exact h1 j ((Finsupp.toMultiset_eq_iff.mp hj).trans (Multiset.toFinsupp_singleton j))
  · exact hge

/-- Every substituted monomial of total degree at least two moves by at least `ρ + ε`. -/
theorem add_le_orderTop_prod_pow_sub [Fintype σ] (a b : σ → R⟦Γ⟧) {ρ ε : WithTop Γ}
    (hε : 0 ≤ ε) (ha : ∀ j, ε ≤ (a j).orderTop) (hb : ∀ j, ε ≤ (b j).orderTop)
    (hab : ∀ j, ρ ≤ (a j - b j).orderTop) (e : σ →₀ ℕ)
    (he : 2 ≤ Multiset.card e.toMultiset) :
    ρ + ε ≤ (∏ i, a i ^ e i - ∏ i, b i ^ e i).orderTop := by
  rw [prod_pow_eq_prod_map_toMultiset, prod_pow_eq_prod_map_toMultiset]
  refine le_trans ?_ (add_le_orderTop_prod_map_sub a b hε ha hb hab e.toMultiset)
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card e.toMultiset - 1 = k + 1 :=
    ⟨Multiset.card e.toMultiset - 2, by omega⟩
  rw [hk, succ_nsmul']
  exact add_le_add le_rfl (le_add_of_nonneg_right (nsmul_nonneg hε k))

/-! ### The vector valuation -/

section Vector

variable [Fintype σ]

/-- The vector valuation `𝐯(a) = min_j v(a_j)` of a finite vector of Hahn series, with
`v(0) = ⊤`; the zero vector (and the empty vector) has valuation `⊤`. This is the notation `𝐯`
of `tate:node:sec:metric`. -/
def vecOrderTop (a : σ → R⟦Γ⟧) : WithTop Γ :=
  Finset.univ.inf fun j => (a j).orderTop

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem le_vecOrderTop_iff {a : σ → R⟦Γ⟧} {g : WithTop Γ} :
    g ≤ vecOrderTop a ↔ ∀ j, g ≤ (a j).orderTop := by
  simp [vecOrderTop, Finset.le_inf_iff]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem vecOrderTop_le (a : σ → R⟦Γ⟧) (j : σ) : vecOrderTop a ≤ (a j).orderTop :=
  Finset.inf_le (Finset.mem_univ j)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- A constant matrix never decreases the vector valuation. -/
theorem vecOrderTop_le_vecOrderTop_smul_sum (L : Matrix σ σ R) (w : σ → R⟦Γ⟧) :
    vecOrderTop w ≤ vecOrderTop fun i => ∑ j, L i j • w j :=
  le_vecOrderTop_iff.mpr fun _ => le_orderTop_finset_sum _ _ fun j _ =>
    (vecOrderTop_le w j).trans (orderTop_le_orderTop_smul _ _)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
private theorem smul_sum_smul_sum (M N : Matrix σ σ R) (w : σ → R⟦Γ⟧) (i : σ) :
    ∑ j, M i j • ∑ k, N j k • w k = ∑ k, (M * N) i k • w k := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- An invertible constant matrix preserves the vector valuation. -/
theorem vecOrderTop_smul_sum [DecidableEq σ] {L : Matrix σ σ R} (hL : IsUnit L)
    (w : σ → R⟦Γ⟧) : vecOrderTop (fun i => ∑ j, L i j • w j) = vecOrderTop w := by
  obtain ⟨u, rfl⟩ := hL
  refine le_antisymm ?_ (vecOrderTop_le_vecOrderTop_smul_sum _ w)
  have hw : (fun i => ∑ j, (↑u⁻¹ : Matrix σ σ R) i j • ∑ k, (u : Matrix σ σ R) j k • w k) =
      w := by
    funext i
    rw [smul_sum_smul_sum, Units.inv_mul]
    simp [Matrix.one_apply]
  calc vecOrderTop (fun i => ∑ j, (u : Matrix σ σ R) i j • w j)
      ≤ vecOrderTop (fun i => ∑ j, (↑u⁻¹ : Matrix σ σ R) i j •
          ∑ k, (u : Matrix σ σ R) j k • w k) :=
        vecOrderTop_le_vecOrderTop_smul_sum _ _
    _ = vecOrderTop w := by rw [hw]

end Vector

/-! ### Linear and nonlinear parts of a formal chart -/

/-- The linear part `L_A` of a formal chart `A = (A_1, …, A_d)`: its `(i, j)` entry is the
coefficient of `Z_j` in `A_i`. -/
def linearPart (A : σ → MvPowerSeries σ R) : Matrix σ σ R :=
  Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (A i)

variable [Fintype σ]

/-- The part of `A_i` of total degree at least two: `A_i` minus its constant and linear
terms. -/
def nonlinearPart (A : σ → MvPowerSeries σ R) (i : σ) : MvPowerSeries σ R :=
  A i - MvPowerSeries.C (MvPowerSeries.constantCoeff (A i)) -
    ∑ j, linearPart A i j • MvPowerSeries.X j

theorem coeff_nonlinearPart_zero (A : σ → MvPowerSeries σ R) (i : σ) :
    MvPowerSeries.coeff 0 (nonlinearPart A i) = 0 := by
  classical
  simp [nonlinearPart, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_nonlinearPart_single (A : σ → MvPowerSeries σ R) (i k : σ) :
    MvPowerSeries.coeff (Finsupp.single k 1) (nonlinearPart A i) = 0 := by
  classical
  simp [nonlinearPart, linearPart, MvPowerSeries.coeff_C, MvPowerSeries.coeff_X,
    Finsupp.single_left_inj]

/-- Strong evaluation splits into constant, linear and nonlinear contributions. -/
theorem mvEvaluate_eq_linear_add_nonlinear (A : σ → MvPowerSeries σ R) (x : σ → R⟦Γ⟧)
    (hx : ∀ j, 0 < (x j).orderTop) (i : σ) :
    mvEvaluate x hx (A i) = single 0 (MvPowerSeries.constantCoeff (A i)) +
      ∑ j, linearPart A i j • x j + mvEvaluate x hx (nonlinearPart A i) := by
  have h : A i = MvPowerSeries.C (MvPowerSeries.constantCoeff (A i)) +
      ∑ j, linearPart A i j • MvPowerSeries.X j + nonlinearPart A i := by
    rw [nonlinearPart]
    abel
  conv_lhs => rw [h]
  simp only [map_add, map_sum, map_smul, mvEvaluate_C, mvEvaluate_X]

theorem mvEvaluate_sub_eq (A : σ → MvPowerSeries σ R) (a b : σ → R⟦Γ⟧)
    (ha : ∀ j, 0 < (a j).orderTop) (hb : ∀ j, 0 < (b j).orderTop) (i : σ) :
    mvEvaluate a ha (A i) - mvEvaluate b hb (A i) =
      ∑ j, linearPart A i j • (a j - b j) +
        (mvEvaluate a ha (nonlinearPart A i) - mvEvaluate b hb (nonlinearPart A i)) := by
  rw [mvEvaluate_eq_linear_add_nonlinear A a ha i, mvEvaluate_eq_linear_add_nonlinear A b hb i]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

/-- The nonlinear part moves by at least `ρ + ε`, where `ρ` bounds the coordinate differences
from below and `ε ≥ 0` bounds all coordinates of `a` and `b` from below. -/
theorem add_le_orderTop_mvEvaluate_nonlinearPart_sub (A : σ → MvPowerSeries σ R)
    (a b : σ → R⟦Γ⟧) (ha : ∀ j, 0 < (a j).orderTop) (hb : ∀ j, 0 < (b j).orderTop)
    {ρ ε : WithTop Γ} (hε : 0 ≤ ε) (hεa : ∀ j, ε ≤ (a j).orderTop)
    (hεb : ∀ j, ε ≤ (b j).orderTop) (hρ : ∀ j, ρ ≤ (a j - b j).orderTop) (i : σ) :
    ρ + ε ≤
      (mvEvaluate a ha (nonlinearPart A i) - mvEvaluate b hb (nonlinearPart A i)).orderTop := by
  rw [mvEvaluate_apply, mvEvaluate_apply, ← SummableFamily.hsum_sub]
  refine le_orderTop_hsum _ fun e => ?_
  rw [SummableFamily.sub_apply, mvEvaluationFamily_apply, mvEvaluationFamily_apply, ← smul_sub]
  by_cases hc : MvPowerSeries.coeff e (nonlinearPart A i) = 0
  · simp [hc]
  refine le_trans ?_ (orderTop_le_orderTop_smul _ _)
  refine add_le_orderTop_prod_pow_sub a b hε hεa hεb hρ e (two_le_card_toMultiset ?_ ?_)
  · rintro rfl
    exact hc (coeff_nonlinearPart_zero A i)
  · rintro j rfl
    exact hc (coeff_nonlinearPart_single A i j)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem vecOrderTop_of_isEmpty [IsEmpty σ] (a : σ → R⟦Γ⟧) : vecOrderTop a = ⊤ := by
  simp [vecOrderTop]

private theorem lt_add_of_ne_top_of_pos {ρ ε : WithTop Γ} (hρ : ρ ≠ ⊤) (hε : 0 < ε) :
    ρ < ρ + ε := by
  simpa using WithTop.add_lt_add_left hρ hε

/-! ### The isometry -/

/-- **Valuation isometry for formal charts** (`tate:node:lem:isometry`). Let
`A ∈ R[[Z_j : j ∈ σ]]^σ` have invertible linear part `L_A`. Then for all vectors `a, b` of
positive-order Hahn series, strong evaluation satisfies `𝐯(A(a) - A(b)) = 𝐯(a - b)`, where
`𝐯(w) = min_j v(w_j)` (equation `tate:node:eq:isometry`). This includes the case `a = b`,
where both sides are `⊤`.

The coefficient ring is any commutative ring, `Γ` is any linearly ordered cancellative
commutative monoid, and no zero-constant-term hypothesis on `A` is needed. -/
theorem vecOrderTop_mvEvaluate_sub [DecidableEq σ] (A : σ → MvPowerSeries σ R)
    (hL : IsUnit (linearPart A)) (a b : σ → R⟦Γ⟧) (ha : ∀ j, 0 < (a j).orderTop)
    (hb : ∀ j, 0 < (b j).orderTop) :
    vecOrderTop (fun i => mvEvaluate a ha (A i) - mvEvaluate b hb (A i)) =
      vecOrderTop (a - b) := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · rw [vecOrderTop_of_isEmpty, vecOrderTop_of_isEmpty]
  obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε : WithTop Γ, 0 < ε ∧ (∀ j, ε ≤ (a j).orderTop) ∧
      ∀ j, ε ≤ (b j).orderTop :=
    ⟨Finset.univ.inf fun j => min (a j).orderTop (b j).orderTop,
      (Finset.lt_inf_iff (WithTop.coe_lt_top (0 : Γ))).mpr fun j _ => lt_min (ha j) (hb j),
      fun j => (Finset.inf_le (Finset.mem_univ j)).trans (min_le_left _ _),
      fun j => (Finset.inf_le (Finset.mem_univ j)).trans (min_le_right _ _)⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, vecOrderTop (a - b) = ρ := ⟨_, rfl⟩
  have hρ : ∀ j, ρ ≤ (a j - b j).orderTop := fun j => hρdef ▸ vecOrderTop_le (a - b) j
  have hlin : vecOrderTop (fun i => ∑ j, linearPart A i j • (a j - b j)) = ρ :=
    (vecOrderTop_smul_sum hL (a - b)).trans hρdef
  have hnon := fun i =>
    add_le_orderTop_mvEvaluate_nonlinearPart_sub A a b ha hb hε.le hεa hεb hρ i
  rw [hρdef]
  refine le_antisymm ?_ ?_
  · by_cases hρtop : ρ = ⊤
    · rw [hρtop]
      exact le_top
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
      fun i => (∑ j, linearPart A i j • (a j - b j)).orderTop
    have hi' : (∑ j, linearPart A i j • (a j - b j)).orderTop = ρ := hi.symm.trans hlin
    calc vecOrderTop (fun i => mvEvaluate a ha (A i) - mvEvaluate b hb (A i))
        ≤ (mvEvaluate a ha (A i) - mvEvaluate b hb (A i)).orderTop := vecOrderTop_le _ i
      _ = ρ := by
        rw [mvEvaluate_sub_eq, orderTop_add_eq_left, hi']
        rw [hi']
        exact (lt_add_of_ne_top_of_pos hρtop hε).trans_le (hnon i)
  · refine le_vecOrderTop_iff.mpr fun i => ?_
    rw [mvEvaluate_sub_eq]
    refine le_trans (le_min ?_ ?_) min_orderTop_le_orderTop_add
    · exact hlin.ge.trans (vecOrderTop_le _ i)
    · exact (le_add_of_nonneg_right hε.le).trans (hnon i)

end

/-- `tate:node:lem:isometry` in the source's setting: `k` is a field, `Γ` an ordered abelian
group, `A ∈ k[[Z_1, …, Z_d]]^d` with `L_A ∈ GL_d(k)`, and `a, b ∈ m_v^d`. The source also
assumes that `A` has zero constant term; this is not needed. The source's standing hypothesis
that `k` has characteristic zero is not assumed either. -/
theorem isometry_of_det_ne_zero {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Field k] {d : ℕ} (A : Fin d → MvPowerSeries (Fin d) k)
    (hL : (linearPart A).det ≠ 0) (a b : Fin d → k⟦Γ⟧) (ha : ∀ j, 0 < (a j).orderTop)
    (hb : ∀ j, 0 < (b j).orderTop) :
    vecOrderTop (fun i => mvEvaluate a ha (A i) - mvEvaluate b hb (A i)) =
      vecOrderTop (a - b) :=
  vecOrderTop_mvEvaluate_sub A
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)) a b ha hb

end Surreal.ChartIsometry
