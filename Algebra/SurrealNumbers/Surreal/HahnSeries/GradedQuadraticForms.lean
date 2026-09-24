import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Square-class multiplicities of positive diagonal forms

This file proves `spec:hank:lem:graded` of `docs/surcomplex/spectral-theory/article.tex`.
Let `φ` be a positive definite quadratic form over `F_Γ = ℝ((t^Γ))`. In any diagonal expression
`φ(x) = a₁x₁² + ⋯ + aₙxₙ²` with all `aⱼ > 0`, the number of indices with `v(aⱼ) + 2Γ = ξ`
depends only on `φ` and `ξ`.

The proof follows the source. The source filters `V` by the half-valuation `w_φ = v(φ)/2` and
computes the constant-field dimension of `gr_η = V_{≥η}/V_{>η}`. We use doubled levels
`c = 2η ∈ Γ`, so that no halving or divisibility of `Γ` is needed:
`V_{≥c} = {x | c ≤ v(φ x)}` and `V_{>c} = {x | c < v(φ x)}`. These are the `k`-spans `levelGE`
and `levelGT`, and `gradedDim k v φ c` is the `k`-dimension of their quotient, a quantity
defined from `φ` alone. Once `φ` has a diagonal expression satisfying `spec:hank:eq:formval`,
`coe_levelGE` and `coe_levelGT` show that the spans are exactly these sets.

## Generic layer

`F` is a commutative `k`-algebra with an additive valuation `v : F → WithTop Γ` into a linearly
ordered abelian group. The structure `GradedCoeff k v` supplies `k`-linear coefficient
functionals `coeff g` on `F`, which induce isomorphisms `F_{≥g}/F_{>g} ≃ k`. For a quadratic
form with a diagonal expression `φ x = ∑ aᵢ (e x)ᵢ²` satisfying `spec:hank:eq:formval`,
`gradedDim_eq_card` proves `gradedDim k v φ c = #{i | v(aᵢ) ∈ c + 2Γ}`. As in the source, the
coefficients of the coordinates at the exponents `(c - v(aᵢ))/2`, where these lie in `Γ`, give
a surjective `k`-linear map `V_{≥c} → k^{J_c}` with kernel `V_{>c}`.

## Hahn layer

Here `F = R⟦Γ⟧` for a linearly ordered field `R` (the source has `R = ℝ`), `k = R`, `v` is
`HahnSeries.addVal`, and the order is the lexicographic one. `orderTop_sum_of_nonneg` proves
`spec:hank:eq:formval` for nonnegative weights. The main results are:

* `gradedDim_eq_card_squareClass`: the count of a nonnegative diagonal expression equals the
  intrinsic graded dimension of `φ`;
* `card_squareClass_eq`: `spec:hank:lem:graded`, stated for two diagonal expressions of the
  same form, given as isometries to `QuadraticMap.weightedSumSquares`;
* `card_squareClass_quotient_eq`: the same statement for classes `ξ : Γ ⧸ 2Γ`;
* `card_squareClass_eq_of_congr` and `card_squareClass_quotient_eq_of_congr`: a matrix
  reformulation through `Pᵀ diag(a) P = diag(b)`, counted by representatives `c` of the class
  `c + 2Γ` and by classes `ξ` respectively. The source states only the diagonal-expression form.

The results hold for every linearly ordered abelian group `Γ` (no divisibility, as in the
source section) and every linearly ordered coefficient field `R`. Nonnegative weights suffice,
so the invariance also holds for positive semidefinite diagonal forms. The source's
positive-definiteness hypothesis enters only through the positivity of the diagonal weights.
The applications of this lemma, `spec:hank:thm:profile` and the factor count
`spec:hank:eq:factorcount`, need `spec:hank:lem:intermediate` and the trace-form
diagonalizations; they are not claimed here.
-/

namespace Surreal.GradedQuadratic

open Finset QuadraticMap

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

section Generic

variable (k : Type*) {F : Type*} [Field k] [CommRing F] [Algebra k F]

/-- Graded coefficient data for an additive valuation `v` on a `k`-algebra `F`. For each
exponent `g`, the `k`-linear functional `coeff g` vanishes on `F_{>g}`, is nonzero on elements of
valuation exactly `g`, and is onto `k` already on `F_{≥g}`. In particular, it induces an
isomorphism `F_{≥g}/F_{>g} ≃ k` (not constructed separately here). Conversely, extending such an
induced functional from `F_{≥g}` to `F` (`LinearMap.exists_extend`) recovers these data; this is
not formalized here. For Hahn series it is the coefficient of `t^g`. -/
structure GradedCoeff (v : AddValuation F (WithTop Γ)) where
  /-- The coefficient functional at the exponent `g`. -/
  coeff : Γ → F →ₗ[k] k
  coeff_eq_zero_of_lt : ∀ (g : Γ) (x : F), (g : WithTop Γ) < v x → coeff g x = 0
  coeff_ne_zero : ∀ (g : Γ) (x : F), v x = g → coeff g x ≠ 0
  exists_coeff_eq : ∀ (g : Γ) (r : k), ∃ x : F, (g : WithTop Γ) ≤ v x ∧ coeff g x = r

variable {k} {v : AddValuation F (WithTop Γ)}

namespace GradedCoeff

/-- Constants from the coefficient field have nonnegative valuation. -/
theorem valuation_algebraMap_nonneg (G : GradedCoeff k v) (r : k) :
    0 ≤ v (algebraMap k F r) := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨x, hx0, hx1⟩ := G.exists_coeff_eq 0 1
  rw [WithTop.coe_zero] at hx0
  have hvx : v x = 0 := by
    refine le_antisymm ?_ hx0
    by_contra hlt
    rw [not_le, ← WithTop.coe_zero] at hlt
    have h := G.coeff_eq_zero_of_lt 0 x hlt
    rw [hx1] at h
    exact one_ne_zero h
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
  have hy : v (r • x) = g := by
    rw [Algebra.smul_def, v.map_mul, hvx, add_zero, hg]
  have hgx : (g : WithTop Γ) < v x := by
    rw [hvx, hg]
    exact hneg
  apply G.coeff_ne_zero g (r • x) hy
  rw [map_smul, G.coeff_eq_zero_of_lt g x hgx, smul_zero]

end GradedCoeff

theorem valuation_mul_sq (a y : F) : v (a * y ^ 2) = v a + (v y + v y) := by
  rw [v.map_mul, pow_two, v.map_mul]

theorem min_le_valuation_mul_sq_add (a y z : F) :
    min (v (a * y ^ 2)) (v (a * z ^ 2)) ≤ v (a * (y + z) ^ 2) := by
  have h := v.map_add y z
  simp only [valuation_mul_sq]
  rcases le_total (v y) (v z) with hyz | hyz
  · rw [min_eq_left hyz] at h
    exact (min_le_left _ _).trans (by gcongr)
  · rw [min_eq_right hyz] at h
    exact (min_le_right _ _).trans (by gcongr)

theorem valuation_mul_sq_le_smul (G : GradedCoeff k v) (a y : F) (r : k) :
    v (a * y ^ 2) ≤ v (a * (r • y) ^ 2) := by
  have h0 := G.valuation_algebraMap_nonneg r
  rw [Algebra.smul_def, show a * (algebraMap k F r * y) ^ 2 =
    (algebraMap k F r * algebraMap k F r) * (a * y ^ 2) by ring,
    v.map_mul (_ * _) (a * y ^ 2), v.map_mul (algebraMap k F r)]
  exact le_add_of_nonneg_left (add_nonneg h0 h0)

/-- A coordinate with `v(a) = c + 2h` reaches level `c` exactly when `v(y) ≥ -h`. -/
theorem le_valuation_mul_sq_iff {a : F} {c h : Γ} (ha : v a = ↑(c + 2 • h)) (y : F) :
    (c : WithTop Γ) ≤ v (a * y ^ 2) ↔ ((-h : Γ) : WithTop Γ) ≤ v y := by
  rw [valuation_mul_sq, ha]
  by_cases hy : v y = ⊤
  · rw [hy, WithTop.add_top, WithTop.add_top]
    exact iff_of_true le_top le_top
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy
  rw [← hb, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe,
    show c + 2 • h + (b + b) = c + ((h + b) + (h + b)) by rw [two_nsmul]; abel,
    le_add_iff_nonneg_right, neg_le_iff_add_nonneg']
  constructor
  · intro H
    by_contra H'
    rw [not_le] at H'
    exact (not_le.mpr (add_neg H' H')) H
  · intro H
    exact add_nonneg H H

/-- A coordinate with `v(a) = c + 2h` lies strictly above level `c` exactly when `v(y) > -h`. -/
theorem lt_valuation_mul_sq_iff {a : F} {c h : Γ} (ha : v a = ↑(c + 2 • h)) (y : F) :
    (c : WithTop Γ) < v (a * y ^ 2) ↔ ((-h : Γ) : WithTop Γ) < v y := by
  rw [valuation_mul_sq, ha]
  by_cases hy : v y = ⊤
  · rw [hy, WithTop.add_top, WithTop.add_top]
    exact iff_of_true (WithTop.coe_lt_top _) (WithTop.coe_lt_top _)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hy
  rw [← hb, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe, WithTop.coe_lt_coe,
    show c + 2 • h + (b + b) = c + ((h + b) + (h + b)) by rw [two_nsmul]; abel,
    lt_add_iff_pos_right, neg_lt_iff_pos_add']
  constructor
  · intro H
    by_contra H'
    rw [not_lt] at H'
    exact (not_lt.mpr (add_nonpos H' H')) H
  · intro H
    exact add_pos H H

/-- A coordinate whose weight has valuation outside `c + 2Γ` never sits exactly at level `c`. -/
theorem valuation_mul_sq_ne {a : F} {c : Γ} (ha : ¬ ∃ g : Γ, v a = ↑(c + 2 • g)) (y : F) :
    v (a * y ^ 2) ≠ c := by
  intro H
  rw [valuation_mul_sq] at H
  by_cases hva : v a = ⊤
  · rw [hva, WithTop.top_add] at H
    exact WithTop.top_ne_coe H
  obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp hva
  by_cases hvy : v y = ⊤
  · rw [hvy, WithTop.add_top, WithTop.add_top] at H
    exact WithTop.top_ne_coe H
  obtain ⟨β, hβ⟩ := WithTop.ne_top_iff_exists.mp hvy
  rw [← hα, ← hβ, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_eq_coe] at H
  exact ha ⟨-β, by rw [← hα, WithTop.coe_eq_coe, ← H, two_nsmul]; abel⟩

section Space

variable {V : Type*} [AddCommGroup V] [Module F V] [Module k V] [IsScalarTower k F V]
  {ι : Type*} [Fintype ι]

/-- The `k`-subspace of vectors whose weighted coordinates `a i * (e x i)²` all have valuation
in an upward-closed set `P` containing `⊤`. -/
def diagLevel (G : GradedCoeff k v) (e : V ≃ₗ[F] (ι → F)) (a : ι → F)
    (P : WithTop Γ → Prop) (hP : ∀ s t, P s → s ≤ t → P t) (htop : P ⊤) : Submodule k V where
  carrier := {x | ∀ i, P (v (a i * e x i ^ 2))}
  add_mem' {x y} hx hy i := by
    rw [map_add, Pi.add_apply]
    rcases min_choice (v (a i * e x i ^ 2)) (v (a i * e y i ^ 2)) with h | h
    · exact hP _ _ (hx i) (h ▸ min_le_valuation_mul_sq_add _ _ _)
    · exact hP _ _ (hy i) (h ▸ min_le_valuation_mul_sq_add _ _ _)
  zero_mem' i := by
    rw [map_zero, Pi.zero_apply, zero_pow two_ne_zero, mul_zero, v.map_zero]
    exact htop
  smul_mem' r x hx i := by
    have he : e (r • x) = r • e x := (e.restrictScalars k).map_smul r x
    rw [he, Pi.smul_apply]
    exact hP _ _ (hx i) (valuation_mul_sq_le_smul G _ _ r)

omit [Fintype ι] in
theorem mem_diagLevel {G : GradedCoeff k v} {e : V ≃ₗ[F] (ι → F)} {a : ι → F}
    {P : WithTop Γ → Prop} {hP : ∀ s t, P s → s ≤ t → P t} {htop : P ⊤} {x : V} :
    x ∈ diagLevel G e a P hP htop ↔ ∀ i, P (v (a i * e x i ^ 2)) :=
  Iff.rfl

variable (k v)

/-- The level `V_{≥c} = {x | c ≤ v(φ x)}`, taken as a `k`-span. The source's level `V_{≥η}` for
the half-valuation `w_φ = v(φ)/2` is the present level at `c = 2η`. -/
def levelGE (φ : QuadraticForm F V) (c : Γ) : Submodule k V :=
  Submodule.span k {x | (c : WithTop Γ) ≤ v (φ x)}

/-- The strict level `V_{>c} = {x | c < v(φ x)}`, taken as a `k`-span. -/
def levelGT (φ : QuadraticForm F V) (c : Γ) : Submodule k V :=
  Submodule.span k {x | (c : WithTop Γ) < v (φ x)}

/-- The `k`-dimension of the graded piece `gr_c = V_{≥c}/V_{>c}`. It is defined from the form
`φ` alone, without reference to any diagonalization. -/
def gradedDim (φ : QuadraticForm F V) (c : Γ) : ℕ :=
  Module.finrank k
    (↥(levelGE k v φ c) ⧸ (levelGT k v φ c).comap (levelGE k v φ c).subtype)

variable {k v}

theorem setOf_le_eq_diagLevel (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    {x | (c : WithTop Γ) ≤ v (φ x)} = (diagLevel G e a (fun s => (c : WithTop Γ) ≤ s)
      (fun _ _ h h' => h.trans h') le_top : Set V) := by
  ext x
  rw [Set.mem_setOf_eq, SetLike.mem_coe, mem_diagLevel, he, hmin, Finset.le_inf_iff]
  simp only [Finset.mem_univ, true_implies]

theorem setOf_lt_eq_diagLevel (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    {x | (c : WithTop Γ) < v (φ x)} = (diagLevel G e a (fun s => (c : WithTop Γ) < s)
      (fun _ _ h h' => h.trans_le h') (WithTop.coe_lt_top c) : Set V) := by
  ext x
  rw [Set.mem_setOf_eq, SetLike.mem_coe, mem_diagLevel, he, hmin,
    Finset.lt_inf_iff (WithTop.coe_lt_top c)]
  simp only [Finset.mem_univ, true_implies]

theorem levelGE_eq (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    levelGE k v φ c = diagLevel G e a (fun s => (c : WithTop Γ) ≤ s)
      (fun _ _ h h' => h.trans h') le_top := by
  rw [levelGE, setOf_le_eq_diagLevel G e he hmin c, Submodule.span_eq]

theorem levelGT_eq (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    levelGT k v φ c = diagLevel G e a (fun s => (c : WithTop Γ) < s)
      (fun _ _ h h' => h.trans_le h') (WithTop.coe_lt_top c) := by
  rw [levelGT, setOf_lt_eq_diagLevel G e he hmin c, Submodule.span_eq]

/-- With a diagonal expression satisfying `spec:hank:eq:formval`, the span `levelGE` is exactly
the set `{x | c ≤ v(φ x)}`, as in the source. -/
theorem coe_levelGE (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    (levelGE k v φ c : Set V) = {x | (c : WithTop Γ) ≤ v (φ x)} := by
  rw [levelGE_eq G e he hmin c, setOf_le_eq_diagLevel G e he hmin c]

/-- With a diagonal expression satisfying `spec:hank:eq:formval`, the span `levelGT` is exactly
the set `{x | c < v(φ x)}`, as in the source. -/
theorem coe_levelGT (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    (levelGT k v φ c : Set V) = {x | (c : WithTop Γ) < v (φ x)} := by
  rw [levelGT_eq G e he hmin c, setOf_lt_eq_diagLevel G e he hmin c]

/-- The generic graded-dimension formula behind `spec:hank:lem:graded`. Let `φ` have a diagonal
expression `φ x = ∑ aᵢ (e x)ᵢ²` whose valuation is the least valuation of its summands, which is
`spec:hank:eq:formval`. Then the `k`-dimension of `V_{≥c}/V_{>c}` is the number of indices with
`v(aᵢ) ∈ c + 2Γ`. -/
theorem gradedDim_eq_card (G : GradedCoeff k v) {φ : QuadraticForm F V} {a : ι → F}
    (e : V ≃ₗ[F] (ι → F)) (he : ∀ x, φ x = ∑ i, a i * e x i ^ 2)
    (hmin : ∀ y : ι → F, v (∑ i, a i * y i ^ 2) = univ.inf fun i => v (a i * y i ^ 2))
    (c : Γ) :
    gradedDim k v φ c = Nat.card {i : ι // ∃ g : Γ, v (a i) = ↑(c + 2 • g)} := by
  classical
  set J := {i : ι // ∃ g : Γ, v (a i) = ↑(c + 2 • g)}
  set DGE := diagLevel G e a (fun s => (c : WithTop Γ) ≤ s) (fun _ _ h h' => h.trans h') le_top
  set DGT := diagLevel G e a (fun s => (c : WithTop Γ) < s) (fun _ _ h h' => h.trans_le h')
    (WithTop.coe_lt_top c)
  let h : J → Γ := fun j => Classical.choose j.2
  have hspec : ∀ j : J, v (a j.1) = ↑(c + 2 • h j) := fun j => Classical.choose_spec j.2
  -- The coefficient of `t^{-h j}` in the `j`-th coordinate, for every contributing index `j`.
  let L : DGE →ₗ[k] (J → k) := LinearMap.pi fun j =>
    (G.coeff (-h j)) ∘ₗ (LinearMap.proj j.1 : (ι → F) →ₗ[k] F) ∘ₗ
      (e.restrictScalars k).toLinearMap ∘ₗ DGE.subtype
  have hL : ∀ (x : DGE) (j : J), L x j = G.coeff (-h j) (e x j) := fun _ _ => rfl
  have hker : LinearMap.ker L = DGT.comap DGE.subtype := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, mem_diagLevel]
    rw [mem_diagLevel] at hx
    constructor
    · intro H i
      by_cases hi : ∃ g : Γ, v (a i) = ↑(c + 2 • g)
      · have hj : L ⟨x, hx⟩ ⟨i, hi⟩ = 0 := by rw [H]; rfl
        rw [hL] at hj
        have hle := (le_valuation_mul_sq_iff (hspec ⟨i, hi⟩) _).mp (hx i)
        rw [lt_valuation_mul_sq_iff (hspec ⟨i, hi⟩)]
        exact lt_of_le_of_ne hle fun heq => G.coeff_ne_zero _ _ heq.symm hj
      · exact lt_of_le_of_ne (hx i) (valuation_mul_sq_ne hi _).symm
    · intro H
      funext j
      rw [hL]
      exact G.coeff_eq_zero_of_lt _ _ ((lt_valuation_mul_sq_iff (hspec j) _).mp (H j))
  have hsurj : Function.Surjective L := by
    intro r
    choose z hz0 hz1 using fun j : J => G.exists_coeff_eq (-h j) (r j)
    let y : ι → F := fun i =>
      if hi : (∃ g : Γ, v (a i) = ↑(c + 2 • g)) then z ⟨i, hi⟩ else 0
    have hxmem : e.symm y ∈ DGE := by
      rw [mem_diagLevel]
      intro i
      rw [e.apply_symm_apply]
      by_cases hi : ∃ g : Γ, v (a i) = ↑(c + 2 • g)
      · simp only [y, dif_pos hi]
        exact (le_valuation_mul_sq_iff (hspec ⟨i, hi⟩) _).mpr (hz0 _)
      · simp only [y, dif_neg hi, zero_pow two_ne_zero, mul_zero, v.map_zero]
        exact le_top
    refine ⟨⟨e.symm y, hxmem⟩, ?_⟩
    funext j
    rw [hL]
    simp only [LinearEquiv.apply_symm_apply, y, dif_pos j.2]
    exact hz1 j
  rw [gradedDim, levelGE_eq G e he hmin c, levelGT_eq G e he hmin c, ← hker,
    (L.quotKerEquivOfSurjective hsurj).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end Space

end Generic

section Hahn

open HahnSeries

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable (Γ R) in
/-- The Hahn coefficients `x ↦ x_g` are graded coefficients for the order valuation. -/
def hahnGradedCoeff : GradedCoeff R (addVal Γ R) where
  coeff g := HahnSeries.coeff.linearMap g
  coeff_eq_zero_of_lt g x hg := by
    rw [addVal_apply] at hg
    exact coeff_eq_zero_of_lt_orderTop hg
  coeff_ne_zero g x hg := by
    rw [addVal_apply] at hg
    exact coeff_orderTop_ne hg
  exists_coeff_eq g r :=
    ⟨single g r, by rw [addVal_apply]; exact orderTop_single_le, coeff_single_same g r⟩

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [LinearOrder R] [IsStrictOrderedRing R] in
theorem coeff_eq_leadingCoeff {x : R⟦Γ⟧} {g : Γ} (hg : x.orderTop = g) :
    x.coeff g = x.leadingCoeff := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact WithTop.top_ne_coe (orderTop_zero.symm.trans hg)
  rw [leadingCoeff_of_ne_zero hx]
  congr 1
  exact ((WithTop.untop_eq_iff _).mpr hg).symm

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [IsStrictOrderedRing R] in
theorem coeff_nonneg_of_le_orderTop {x : R⟦Γ⟧} (hx : 0 ≤ toLex x) {g : Γ}
    (hg : (g : WithTop Γ) ≤ x.orderTop) : 0 ≤ x.coeff g := by
  rcases hg.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_lt_orderTop hlt]
  · rw [coeff_eq_leadingCoeff heq.symm]
    exact leadingCoeff_nonneg_iff.mpr hx

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [IsStrictOrderedRing R] in
theorem coeff_pos_of_orderTop_eq {x : R⟦Γ⟧} (hx : 0 ≤ toLex x) {g : Γ}
    (hg : x.orderTop = g) : 0 < x.coeff g := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact WithTop.top_ne_coe (orderTop_zero.symm.trans hg)
  have hpos : 0 < toLex x := lt_of_le_of_ne hx fun h => hx0 (by
    rw [← ofLex_toLex x, ← h, ofLex_zero])
  rw [coeff_eq_leadingCoeff hg]
  exact leadingCoeff_pos_iff.mpr hpos

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- A sum of two nonnegative lexicographic Hahn series has the smaller order: the valuation is
convex on the positive cone. -/
theorem orderTop_add_of_nonneg {x y : R⟦Γ⟧} (hx : 0 ≤ toLex x) (hy : 0 ≤ toLex y) :
    (x + y).orderTop = min x.orderTop y.orderTop := by
  refine le_antisymm ?_ min_orderTop_le_orderTop_add
  by_cases htop : min x.orderTop y.orderTop = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hg]
  apply orderTop_le_of_coeff_ne_zero
  rw [coeff_add]
  have hgx : (g : WithTop Γ) ≤ x.orderTop := hg ▸ min_le_left _ _
  have hgy : (g : WithTop Γ) ≤ y.orderTop := hg ▸ min_le_right _ _
  rcases min_choice x.orderTop y.orderTop with h | h
  · exact (add_pos_of_pos_of_nonneg (coeff_pos_of_orderTop_eq hx (h.symm.trans hg.symm))
      (coeff_nonneg_of_le_orderTop hy hgy)).ne'
  · exact (add_pos_of_nonneg_of_pos (coeff_nonneg_of_le_orderTop hx hgx)
      (coeff_pos_of_orderTop_eq hy (h.symm.trans hg.symm))).ne'

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- A finite sum of nonnegative lexicographic Hahn series is nonnegative and has the least
order of its summands. -/
theorem orderTop_sum_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → R⟦Γ⟧)
    (hf : ∀ i ∈ s, 0 ≤ toLex (f i)) :
    0 ≤ toLex (∑ i ∈ s, f i) ∧ (∑ i ∈ s, f i).orderTop = s.inf fun i => (f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨h0, h1⟩ := ih fun j hj => hf j (mem_insert_of_mem hj)
    have hfi := hf i (mem_insert_self i s)
    rw [sum_insert hi, inf_insert, toLex_add, orderTop_add_of_nonneg hfi h0, h1]
    exact ⟨add_nonneg hfi h0, rfl⟩

theorem toLex_mul_sq_nonneg {a : R⟦Γ⟧} (ha : 0 ≤ toLex a) (y : R⟦Γ⟧) :
    0 ≤ toLex (a * y ^ 2) := by
  rw [toLex_mul, toLex_pow]
  exact mul_nonneg ha (sq_nonneg _)

/-- `spec:hank:eq:formval`: for nonnegative weights, the valuation of a diagonal form is the
least valuation of its summands. -/
theorem addVal_sum_mul_sq {ι : Type*} [Fintype ι] {a : ι → R⟦Γ⟧} (ha : ∀ i, 0 ≤ toLex (a i))
    (y : ι → R⟦Γ⟧) :
    addVal Γ R (∑ i, a i * y i ^ 2) = univ.inf fun i => addVal Γ R (a i * y i ^ 2) := by
  simp only [addVal_apply]
  exact (orderTop_sum_of_nonneg _ _ fun i _ => toLex_mul_sq_nonneg (ha i) (y i)).2

section Forms

variable {V : Type*} [AddCommGroup V] [Module R⟦Γ⟧ V]

/-- `spec:hank:lem:graded`, graded-dimension form. Let `e` be a diagonal expression of `φ`
with nonnegative weights `aᵢ`, that is, an isometry from `φ` to `∑ aᵢ xᵢ²`. Then the number of
indices with `v(aᵢ) ∈ c + 2Γ` equals the `R`-dimension of `V_{≥c}/V_{>c}`, which depends only on
`φ` and `c`. -/
theorem gradedDim_eq_card_squareClass [Module R V] [IsScalarTower R R⟦Γ⟧ V]
    {φ : QuadraticForm R⟦Γ⟧ V} {ι : Type*} [Fintype ι] {a : ι → R⟦Γ⟧}
    (ha : ∀ i, 0 ≤ toLex (a i)) (e : φ.IsometryEquiv (weightedSumSquares R⟦Γ⟧ a)) (c : Γ) :
    gradedDim R (addVal Γ R) φ c =
      Nat.card {i : ι // ∃ g : Γ, (a i).orderTop = ↑(c + 2 • g)} := by
  have he : ∀ x, φ x = ∑ i, a i * (e : V ≃ₗ[R⟦Γ⟧] (ι → R⟦Γ⟧)) x i ^ 2 := by
    intro x
    rw [← e.map_app x, weightedSumSquares_apply]
    simp only [smul_eq_mul, pow_two, IsometryEquiv.coe_toLinearEquiv]
  simpa only [addVal_apply] using
    gradedDim_eq_card (hahnGradedCoeff Γ R) (e : V ≃ₗ[R⟦Γ⟧] (ι → R⟦Γ⟧)) he
      (addVal_sum_mul_sq ha) c

/-- `spec:hank:lem:graded`: square-class multiplicities are congruence invariants. Two diagonal
expressions `φ ≅ ∑ aᵢ xᵢ²` and `φ ≅ ∑ bⱼ yⱼ²` of the same form with nonnegative (in the source,
positive) weights have, for every `c : Γ`, the same number of weights with valuation in the
class `c + 2Γ`. -/
theorem card_squareClass_eq {φ : QuadraticForm R⟦Γ⟧ V} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → R⟦Γ⟧} {b : κ → R⟦Γ⟧} (ha : ∀ i, 0 ≤ toLex (a i)) (hb : ∀ j, 0 ≤ toLex (b j))
    (ea : φ.IsometryEquiv (weightedSumSquares R⟦Γ⟧ a))
    (eb : φ.IsometryEquiv (weightedSumSquares R⟦Γ⟧ b)) (c : Γ) :
    Nat.card {i : ι // ∃ g : Γ, (a i).orderTop = ↑(c + 2 • g)} =
      Nat.card {j : κ // ∃ g : Γ, (b j).orderTop = ↑(c + 2 • g)} := by
  rw [← gradedDim_eq_card_squareClass ha (eb.symm.trans ea) c,
    gradedDim_eq_card_squareClass hb (IsometryEquiv.refl _) c]

end Forms

variable (Γ) in
/-- The subgroup `2Γ` of doubles. -/
def twoMulSubgroup : AddSubgroup Γ :=
  (nsmulAddMonoidHom 2 : Γ →+ Γ).range

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
theorem mem_twoMulSubgroup {x : Γ} : x ∈ twoMulSubgroup Γ ↔ ∃ g : Γ, 2 • g = x :=
  AddMonoidHom.mem_range

omit [IsOrderedAddMonoid Γ] [LinearOrder R] [IsStrictOrderedRing R] in
/-- A nonzero series has valuation class `c + 2Γ` in `Γ ⧸ 2Γ` exactly when its valuation lies in
`c + 2Γ`. -/
theorem squareClass_mk_eq_iff {x : R⟦Γ⟧} {c : Γ} :
    (x ≠ 0 ∧ (QuotientAddGroup.mk x.order : Γ ⧸ twoMulSubgroup Γ) = QuotientAddGroup.mk c) ↔
      ∃ g : Γ, x.orderTop = ↑(c + 2 • g) := by
  constructor
  · rintro ⟨hx, hq⟩
    obtain ⟨g, hg⟩ := mem_twoMulSubgroup.mp (QuotientAddGroup.eq.mp hq)
    refine ⟨-g, ?_⟩
    rw [← order_eq_orderTop_of_ne_zero hx, WithTop.coe_eq_coe, smul_neg, hg]
    abel
  · rintro ⟨g, hg⟩
    have hx : x ≠ 0 := by
      rintro rfl
      exact WithTop.top_ne_coe (orderTop_zero.symm.trans hg)
    have hord : x.order = c + 2 • g := by
      rw [← WithTop.coe_eq_coe, order_eq_orderTop_of_ne_zero hx, hg]
    refine ⟨hx, QuotientAddGroup.eq.mpr (mem_twoMulSubgroup.mpr ⟨-g, ?_⟩)⟩
    rw [hord, smul_neg]
    abel

variable {V : Type*} [AddCommGroup V] [Module R⟦Γ⟧ V]

/-- `spec:hank:lem:graded`, stated with classes `ξ ∈ Γ/2Γ`: in any diagonal expression with
nonnegative (in the source, positive) weights, the number of nonzero weights `aᵢ` with
`v(aᵢ) + 2Γ = ξ` depends only on `φ` and `ξ`. -/
theorem card_squareClass_quotient_eq {φ : QuadraticForm R⟦Γ⟧ V} {ι κ : Type*} [Fintype ι]
    [Fintype κ] {a : ι → R⟦Γ⟧} {b : κ → R⟦Γ⟧} (ha : ∀ i, 0 ≤ toLex (a i))
    (hb : ∀ j, 0 ≤ toLex (b j)) (ea : φ.IsometryEquiv (weightedSumSquares R⟦Γ⟧ a))
    (eb : φ.IsometryEquiv (weightedSumSquares R⟦Γ⟧ b)) (ξ : Γ ⧸ twoMulSubgroup Γ) :
    Nat.card {i : ι // a i ≠ 0 ∧ (QuotientAddGroup.mk (a i).order : Γ ⧸ _) = ξ} =
      Nat.card {j : κ // b j ≠ 0 ∧ (QuotientAddGroup.mk (b j).order : Γ ⧸ _) = ξ} := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun i => squareClass_mk_eq_iff (x := a i)),
    Nat.card_congr (Equiv.subtypeEquivRight fun j => squareClass_mk_eq_iff (x := b j))]
  exact card_squareClass_eq ha hb ea eb c

omit [LinearOrder R] [IsStrictOrderedRing R] in
open Matrix in
theorem weightedSumSquares_eq_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a y : ι → R⟦Γ⟧) :
    weightedSumSquares R⟦Γ⟧ a y = y ⬝ᵥ (Matrix.diagonal a *ᵥ y) := by
  rw [weightedSumSquares_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal, smul_eq_mul]
  ring

open Matrix in
/-- Matrix reformulation of `spec:hank:lem:graded` (the source states only the
diagonal-expression form, whose weights are all positive): if `Pᵀ diag(a) P = diag(b)` with
`aᵢ ≥ 0` and `bᵢ > 0`, then for every `c : Γ`, which represents the class `c + 2Γ`, `diag(a)` and
`diag(b)` have the same number of entries with valuation in `c + 2Γ`. Invertibility of `P` is
not assumed; it follows from the positivity of `b`. -/
theorem card_squareClass_eq_of_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → R⟦Γ⟧} (ha : ∀ i, 0 ≤ toLex (a i)) (hb : ∀ i, 0 < toLex (b i))
    (P : Matrix ι ι R⟦Γ⟧) (h : P.transpose * Matrix.diagonal a * P = Matrix.diagonal b)
    (c : Γ) :
    Nat.card {i : ι // ∃ g : Γ, (a i).orderTop = ↑(c + 2 • g)} =
      Nat.card {i : ι // ∃ g : Γ, (b i).orderTop = ↑(c + 2 • g)} := by
  have hb0 : ∀ i, b i ≠ 0 := fun i hbi => (hb i).ne' (by rw [hbi, toLex_zero])
  have hdet : P.det ≠ 0 := by
    intro hP
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, hP, mul_zero, Matrix.det_diagonal] at this
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb0 i) this.symm
  have hu : IsUnit P.det := Ne.isUnit (G₀ := R⟦Γ⟧) hdet
  letI := P.invertibleOfIsUnitDet hu
  let E : (weightedSumSquares R⟦Γ⟧ b).IsometryEquiv (weightedSumSquares R⟦Γ⟧ a) :=
    { P.toLinearEquiv' this with
      map_app' := fun x => by
        change weightedSumSquares R⟦Γ⟧ a (P *ᵥ x) = weightedSumSquares R⟦Γ⟧ b x
        have key : ∀ w, (P *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (Pᵀ *ᵥ w) := fun w => by
          rw [dotProduct_mulVec, vecMul_transpose]
        rw [weightedSumSquares_eq_dotProduct, weightedSumSquares_eq_dotProduct, key,
          mulVec_mulVec, mulVec_mulVec, h] }
  exact card_squareClass_eq ha (fun i => (hb i).le) E (IsometryEquiv.refl _) c

/-- Matrix reformulation of `spec:hank:lem:graded`, stated with classes `ξ ∈ Γ/2Γ`: if
`Pᵀ diag(a) P = diag(b)` with `aᵢ ≥ 0` and `bᵢ > 0`, then `diag(a)` and `diag(b)` have the same
number of nonzero entries `x` with `v(x) + 2Γ = ξ`. -/
theorem card_squareClass_quotient_eq_of_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → R⟦Γ⟧} (ha : ∀ i, 0 ≤ toLex (a i)) (hb : ∀ i, 0 < toLex (b i))
    (P : Matrix ι ι R⟦Γ⟧) (h : P.transpose * Matrix.diagonal a * P = Matrix.diagonal b)
    (ξ : Γ ⧸ twoMulSubgroup Γ) :
    Nat.card {i : ι // a i ≠ 0 ∧ (QuotientAddGroup.mk (a i).order : Γ ⧸ _) = ξ} =
      Nat.card {i : ι // b i ≠ 0 ∧ (QuotientAddGroup.mk (b i).order : Γ ⧸ _) = ξ} := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun i => squareClass_mk_eq_iff (x := a i)),
    Nat.card_congr (Equiv.subtypeEquivRight fun i => squareClass_mk_eq_iff (x := b i))]
  exact card_squareClass_eq_of_congr ha hb P h c

end Hahn

end

end Surreal.GradedQuadratic
