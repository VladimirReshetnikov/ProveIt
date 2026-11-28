import GRHArticle.ProgressionFree.PolynomialSmoothOptimization
import GRHArticle.ProgressionFree.PolynomialReplacementCount

/-!
# Optimal smooth choices in squarefree rough classes

For each degree budget, choose a maximizing subset of the monic smooth ball.
For every monic squarefree rough part, include every scalar and the chosen
smooth parts for its remaining degree budget.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [instEq : DecidableEq F]

noncomputable def polynomialSmoothOptimizer (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T t : ℕ) : Finset (Polynomial F) :=
  (exists_polynomialSmoothMaximum (F := F) T t).choose

theorem polynomialSmoothOptimizer_properties (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T t : ℕ) :
    polynomialSmoothOptimizer F T t ⊆ polynomialSmoothBall F T t ∧
      PolynomialRatioThreeGPFree (polynomialSmoothOptimizer F T t : Set (Polynomial F)) ∧
      (polynomialSmoothOptimizer F T t).card = polynomialSmoothMaximum F T t :=
  (exists_polynomialSmoothMaximum (F := F) T t).choose_spec

/-- The finite selection with a separate optimal smooth choice in each
squarefree monic rough class. -/
def polynomialSquarefreeTemplateBall {F : Type*} [Field F] (T N : ℕ)
    (H : ℕ → Finset (Polynomial F)) : Set (Polynomial F) :=
  {f | f ≠ 0 ∧ f.natDegree ≤ N ∧ Squarefree (polynomialRoughPart T f) ∧
    polynomialSmoothPart T f ∈ H (N - (polynomialRoughPart T f).natDegree)}

/-- Use a finite optimizer for each remaining degree. -/
def polynomialSquarefreeOptimalBall (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T N : ℕ) : Set (Polynomial F) :=
  polynomialSquarefreeTemplateBall T N (polynomialSmoothOptimizer F T)

omit [Fintype F] [DecidableEq F] in
private theorem roughFactors_mul (T : ℕ) {a b : Polynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    polynomialRoughFactors T (a * b) = polynomialRoughFactors T a + polynomialRoughFactors T b := by
  simp only [polynomialRoughFactors, normalizedFactors_mul ha hb, Multiset.filter_add]

omit [Fintype F] [DecidableEq F] in
private theorem smoothPart_mul (T : ℕ) {a b : Polynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    polynomialSmoothPart T (a * b) = polynomialSmoothPart T a * polynomialSmoothPart T b := by
  simp only [polynomialSmoothPart, normalizedFactors_mul ha hb, Multiset.filter_add, Multiset.prod_add]

/-- Squarefreeness of the final rough part forces the polynomial ratio to
be smooth. The smooth factors would then violate the same chosen optimum. -/
theorem polynomialSquarefreeOptimalBall_free (T N : ℕ) :
    PolynomialRatioThreeGPFree (polynomialSquarefreeOptimalBall F T N) := by
  intro f r hf hr ⟨hfB, hfrB, hfrrB⟩
  have hr₀ : r ≠ 0 := by rintro rfl; simp at hr
  have hfr := mul_ne_zero hf hr₀
  have hR₁ := roughFactors_mul T hf hr₀
  have hR₂ := roughFactors_mul T hfr hr₀
  have hnodup := (squarefree_polynomialRoughPart_iff T (f * r * r)).mp hfrrB.2.2.1
  rw [hR₂, hR₁, add_assoc] at hnodup
  have hR : polynomialRoughFactors T r = 0 := by
    simpa using (Multiset.nodup_add.mp (Multiset.nodup_add.mp hnodup).2.1).2.2
  rw [hR, add_zero] at hR₁ hR₂
  have hrr : polynomialRoughPart T r = 1 := by simp [polynomialRoughPart, hR]
  have hsd := natDegree_roughPart_add_smoothPart T hr₀
  rw [hrr, natDegree_one, zero_add] at hsd
  have hS₁ := smoothPart_mul T hf hr₀
  have hS₂ := smoothPart_mul T hfr hr₀
  have hmem₁ := hfrB.2.2.2
  have hmem₂ := hfrrB.2.2.2
  change polynomialSmoothPart T (f * r) ∈
    polynomialSmoothOptimizer F T (N - (polynomialRoughFactors T (f * r)).prod.natDegree) at hmem₁
  change polynomialSmoothPart T (f * r * r) ∈
    polynomialSmoothOptimizer F T (N - (polynomialRoughFactors T (f * r * r)).prod.natDegree) at hmem₂
  rw [hS₁, hR₁] at hmem₁
  rw [hS₂, hS₁, hR₂, hR₁] at hmem₂
  exact (polynomialSmoothOptimizer_properties F T (N - (polynomialRoughPart T f).natDegree)).2.1
    (polynomialSmoothPart T f) (polynomialSmoothPart T r)
    (monic_polynomialSmoothPart T f).ne_zero (hsd ▸ hr) ⟨hfB.2.2.2, hmem₁, hmem₂⟩

variable (H : ℕ → Finset (Polynomial F))

private noncomputable def squarefreeOptimalBallFinset (T N : ℕ) : Finset (Polynomial F) :=
  (polynomialDegreeLTFinset F (N + 1)).filter (· ∈ polynomialSquarefreeTemplateBall T N H)

private noncomputable def squarefreeOptimalBallFiber (T N t : ℕ) : Finset (Polynomial F) :=
  (squarefreeOptimalBallFinset H T N).filter
    (fun f ↦ N - (polynomialRoughPart T f).natDegree = t)

omit [Fintype F] [DecidableEq F] in
private theorem natDegree_scalar_rough_smooth (c : Fˣ) {g h : Polynomial F}
    (hg : g.Monic) (hh : h.Monic) :
    (C (c : F) * g * h).natDegree = g.natDegree + h.natDegree := by
  rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr c.ne_zero) hg.ne_zero) hh.ne_zero,
    natDegree_C_mul c.ne_zero]

private theorem parts_of_scalar_optimizer_mul {T n t : ℕ} (hH : ∀ j, H j ⊆ polynomialSmoothBall F T j) (c : Fˣ) {g h : Polynomial F}
    (hg : g ∈ polynomialSquarefreeRoughLayer F T n) (hh : h ∈ H t) :
    polynomialRoughPart T (C (c : F) * g * h) = g ∧
      polynomialSmoothPart T (C (c : F) * g * h) = h := by
  have heq : instEq = Classical.decEq F := Subsingleton.elim _ _
  subst instEq
  obtain ⟨hgm, _, _, hgr⟩ := mem_polynomialSquarefreeRoughLayer.mp hg
  obtain ⟨hhm, _, hhr⟩ := mem_polynomialSmoothBall.mp
    (hH t hh)
  exact parts_of_scalar_mul T c hgm hhm hgr hhr

private noncomputable def squarefreeOptimalBallFiberEquiv (T N t : ℕ) (hH : ∀ j, H j ⊆ polynomialSmoothBall F T j) (ht : t ≤ N) :
    (Fˣ × polynomialSquarefreeRoughLayer F T (N - t) × H t) ≃
      squarefreeOptimalBallFiber H T N t := by
  let toFiber (x : Fˣ × polynomialSquarefreeRoughLayer F T (N - t) ×
      H t) : squarefreeOptimalBallFiber H T N t := by
    refine ⟨C (x.1 : F) * x.2.1.1 * x.2.2.1, ?_⟩
    rcases x with ⟨c, ⟨g, hg⟩, ⟨h, hh⟩⟩
    let f := C (c : F) * g * h
    obtain ⟨hgm, hgd, hgs, _⟩ := mem_polynomialSquarefreeRoughLayer.mp hg
    obtain ⟨hhm, hhd, _⟩ := mem_polynomialSmoothBall.mp
      (hH t hh)
    have hf₀ : f ≠ 0 := mul_ne_zero (mul_ne_zero (C_ne_zero.mpr c.ne_zero) hgm.ne_zero) hhm.ne_zero
    have hdeg : f.natDegree ≤ N := by
      dsimp [f]
      rw [natDegree_scalar_rough_smooth c hgm hhm, hgd]
      omega
    obtain ⟨hrough, hsmooth⟩ := parts_of_scalar_optimizer_mul H hH c hg hh
    have hbudget : N - (polynomialRoughPart T f).natDegree = t := by
      change N - (polynomialRoughPart T (C (c : F) * g * h)).natDegree = t
      rw [hrough, hgd]
      omega
    have hmem : f ∈ polynomialSquarefreeTemplateBall T N H := by
      refine ⟨hf₀, hdeg, ?_, ?_⟩
      · simpa only [f, hrough] using hgs
      · rw [hbudget]
        simpa only [f, hsmooth] using hh
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hmem⟩, hbudget⟩
    exact mem_polynomialDegreeLTFinset.mpr
      (by rw [degree_eq_natDegree hf₀, Nat.cast_lt, Nat.lt_succ_iff]; exact hdeg)
  let fromFiber (x : squarefreeOptimalBallFiber H T N t) :
    Fˣ × polynomialSquarefreeRoughLayer F T (N - t) × H t := by
    have hx := Finset.mem_filter.mp x.2
    have hmem := (Finset.mem_filter.mp hx.1).2
    refine ⟨Units.mk0 x.1.leadingCoeff (leadingCoeff_ne_zero.mpr hmem.1),
      ⟨polynomialRoughPart T x.1, ?_⟩, ⟨polynomialSmoothPart T x.1, ?_⟩⟩
    · refine mem_polynomialSquarefreeRoughLayer.mpr
        ⟨monic_polynomialRoughPart T x.1, ?_, hmem.2.2.1, ?_⟩
      · have hpart := natDegree_roughPart_add_smoothPart T hmem.1
        have hbudget := hx.2
        have hdeg := hmem.2.1
        omega
      · rw [normalizedFactors_polynomialRoughPart, polynomialRoughFactors]
        exact fun p hp ↦ (Multiset.mem_filter.mp hp).2
    · have hsm := hmem.2.2.2
      rwa [hx.2] at hsm
  refine ⟨toFiber, fromFiber, ?_, ?_⟩
  · rintro ⟨c, ⟨g, hg⟩, ⟨h, hh⟩⟩
    obtain ⟨hgm, _, _, _⟩ := mem_polynomialSquarefreeRoughLayer.mp hg
    obtain ⟨hhm, _, _⟩ := mem_polynomialSmoothBall.mp
      (hH t hh)
    obtain ⟨hrough, hsmooth⟩ := parts_of_scalar_optimizer_mul H hH c hg hh
    refine Prod.ext (Units.ext ?_) (Prod.ext (Subtype.ext hrough) (Subtype.ext hsmooth))
    change (C (c : F) * g * h).leadingCoeff = (c : F)
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, hgm.leadingCoeff, hhm.leadingCoeff,
      mul_one, mul_one]
  · intro x
    apply Subtype.ext
    exact polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart T x.1

private theorem card_squarefreeOptimalBallFiber (T N t : ℕ) (hH : ∀ j, H j ⊆ polynomialSmoothBall F T j) (ht : t ≤ N) :
    (squarefreeOptimalBallFiber H T N t).card = (Fintype.card F - 1) *
      (polynomialSquarefreeRoughLayer F T (N - t)).card * (H t).card := by
  simpa only [Fintype.card_prod, Fintype.card_units, Fintype.card_coe, mul_assoc] using
    (Fintype.card_congr (squarefreeOptimalBallFiberEquiv H T N t hH ht)).symm

/-- The selected ball counts one product of scalar, squarefree rough, and
optimal smooth choices for each remaining degree. -/
theorem card_polynomialSquarefreeTemplateBall (T N : ℕ) (hH : ∀ j, H j ⊆ polynomialSmoothBall F T j) :
    ((polynomialDegreeLTFinset F (N + 1)).filter (· ∈ polynomialSquarefreeTemplateBall T N H)).card =
      ∑ t ∈ Finset.range (N + 1), (Fintype.card F - 1) *
        (polynomialSquarefreeRoughLayer F T (N - t)).card * (H t).card := by
  change (squarefreeOptimalBallFinset H T N).card = _
  have hmaps : Set.MapsTo (fun f : Polynomial F ↦ N - (polynomialRoughPart T f).natDegree)
      (squarefreeOptimalBallFinset H T N : Set (Polynomial F)) (Finset.range (N + 1)) :=
    fun f _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  exact Finset.sum_congr rfl fun t ht ↦ card_squarefreeOptimalBallFiber H T N t hH
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

theorem card_polynomialSquarefreeOptimalBall (T N : ℕ) :
    ((polynomialDegreeLTFinset F (N + 1)).filter (· ∈ polynomialSquarefreeOptimalBall F T N)).card =
      ∑ t ∈ Finset.range (N + 1), (Fintype.card F - 1) *
        (polynomialSquarefreeRoughLayer F T (N - t)).card * polynomialSmoothMaximum F T t := by
  simpa only [polynomialSquarefreeOptimalBall, (polynomialSmoothOptimizer_properties F T _).2.2] using
    card_polynomialSquarefreeTemplateBall (polynomialSmoothOptimizer F T) T N
      (fun j ↦ (polynomialSmoothOptimizer_properties F T j).1)

end GRHArticle.ProgressionFree
