import Surreal.HahnSeries.NonpositiveSupportUnits
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Polynomial degree growth and algebraic rigidity in Hahn support rings

The remaining clauses of `odg:def:lem:units`: a nonconstant support-ring
series has strictly positive omega-degree, polynomial evaluation multiplies
that degree, every algebraic element is constant, and roots descend to the
constant intersection of any intermediate ring. No ordering or
characteristic restriction on the coefficient field is used.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

attribute [local instance] nonpositiveSupportAlgebra

/-- Negative-order Hahn elements cannot cancel the highest-degree term of a nonzero polynomial. -/
theorem polynomial_eval_negative_order (P : Polynomial K) (hP : P ≠ 0)
    (f : K⟦Γ⟧) (hf : f.order < 0) :
    P.eval₂ _root_.HahnSeries.C f ≠ 0 ∧
      (P.eval₂ _root_.HahnSeries.C f).order = P.natDegree • f.order := by
  classical
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  let t := fun i => _root_.HahnSeries.C (P.coeff i) * f ^ i
  have ht (i : ℕ) (hi : P.coeff i ≠ 0) :
      t i ≠ 0 ∧ (t i).order = i • f.order := by
    have hc : (_root_.HahnSeries.C (P.coeff i) : K⟦Γ⟧) ≠ 0 :=
      by simpa only [map_zero] using (_root_.HahnSeries.C : K →+* K⟦Γ⟧).injective.ne hi
    exact ⟨mul_ne_zero hc (pow_ne_zero i hf0), by
      dsimp [t]
      rw [order_mul hc (pow_ne_zero i hf0), order_C, order_pow, zero_add]⟩
  have hn : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc : (P.eval₂ _root_.HahnSeries.C f).coeff (P.natDegree • f.order) =
      (t P.natDegree).coeff (P.natDegree • f.order) := by
    rw [Polynomial.eval₂_eq_sum_range, coeff_sum]
    apply Finset.sum_eq_single P.natDegree
    · intro i hi hin
      change (t i).coeff _ = 0
      by_cases hz : P.coeff i = 0
      · simp [t, hz]
      · apply coeff_eq_zero_of_lt_order
        rw [(ht i hz).2]
        exact nsmul_lt_nsmul_left (M := Γᵒᵈ) hf
          (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hin)
    · simp
  have hlead : (P.eval₂ _root_.HahnSeries.C f).coeff (P.natDegree • f.order) ≠ 0 := by
    rw [hc, ← (ht P.natDegree hn).2]
    exact coeff_order_eq_zero.not.mpr (ht P.natDegree hn).1
  have he : P.eval₂ _root_.HahnSeries.C f ≠ 0 := ne_zero_of_coeff_ne_zero hlead
  refine ⟨he, le_antisymm (order_le_of_coeff_ne_zero hlead) ?_⟩
  apply (le_order_iff_forall he).mpr
  intro a ha
  rw [Polynomial.eval₂_eq_sum_range, coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  change (t i).coeff a = 0
  by_cases hz : P.coeff i = 0
  · simp [t, hz]
  · apply coeff_eq_zero_of_lt_order
    rw [(ht i hz).2]
    exact ha.trans_le (nsmul_le_nsmul_left_of_nonpos hf.le
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

/-- Nonconstant support-ring series have strictly negative Hahn order. -/
theorem nonpositiveSupport_order_neg_of_nonconstant (f : nonpositiveSupportSubring Γ K)
    (hf : f ≠ nonpositiveConstants (nonpositiveConstantCoeff f)) : f.val.order < 0 := by
  exact lt_of_not_ge (fun h => hf (nonpositiveSupport_eq_constant_of_order_nonneg f h))

/-- Native evaluation in the support ring agrees with evaluation in its ambient Hahn ring. -/
theorem nonpositiveSupport_eval_val (P : Polynomial K) (f : nonpositiveSupportSubring Γ K) :
    (P.eval₂ nonpositiveConstants f).val = P.eval₂ _root_.HahnSeries.C f.val := by
  change (nonpositiveSupportSubring Γ K).subtype (P.eval₂ nonpositiveConstants f) = _
  rw [Polynomial.hom_eval₂]
  rfl

/-- A nonzero polynomial does not vanish at a nonconstant support-ring element. -/
theorem nonpositiveSupport_eval_ne_zero (P : Polynomial K) (hP : P ≠ 0)
    (f : nonpositiveSupportSubring Γ K)
    (hf : f ≠ nonpositiveConstants (nonpositiveConstantCoeff f)) :
    P.eval₂ nonpositiveConstants f ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  rw [nonpositiveSupport_eval_val] at hv
  exact (polynomial_eval_negative_order P hP f.val
    (nonpositiveSupport_order_neg_of_nonconstant f hf)).1 hv

/-- Polynomial evaluation multiplies omega-degree by the native polynomial degree. -/
theorem nonpositiveDegree_eval (P : Polynomial K) (hP : P ≠ 0)
    (f : nonpositiveSupportSubring Γ K)
    (hf : f ≠ nonpositiveConstants (nonpositiveConstantCoeff f)) :
    nonpositiveDegree (P.eval₂ nonpositiveConstants f) = P.natDegree • nonpositiveDegree f := by
  unfold nonpositiveDegree
  rw [nonpositiveSupport_eval_val,
    (polynomial_eval_negative_order P hP f.val
      (nonpositiveSupport_order_neg_of_nonconstant f hf)).2, smul_neg]

/-- Positive-degree polynomial evaluations at nonconstant elements have positive omega-degree. -/
theorem nonpositiveDegree_eval_pos (P : Polynomial K) (hP : 0 < P.natDegree)
    (f : nonpositiveSupportSubring Γ K)
    (hf : f ≠ nonpositiveConstants (nonpositiveConstantCoeff f)) :
    0 < nonpositiveDegree (P.eval₂ nonpositiveConstants f) := by
  rw [nonpositiveDegree_eval P (by intro h; simp [h] at hP) f hf]
  exact nsmul_pos (neg_pos.mpr (nonpositiveSupport_order_neg_of_nonconstant f hf)) hP.ne'

/-- A nonzero coefficient-field polynomial has exactly its constant roots in the support ring. -/
theorem nonpositiveSupport_polynomial_root_iff (P : Polynomial K) (hP : P ≠ 0)
    (f : nonpositiveSupportSubring Γ K) :
    P.eval₂ nonpositiveConstants f = 0 ↔
      ∃ c : K, f = nonpositiveConstants c ∧ P.eval c = 0 := by
  constructor
  · intro h
    have hf : f = nonpositiveConstants (nonpositiveConstantCoeff f) := by
      by_contra hn
      exact nonpositiveSupport_eval_ne_zero P hP f hn h
    refine ⟨nonpositiveConstantCoeff f, hf, ?_⟩
    rw [hf, Polynomial.eval₂_at_apply] at h
    exact nonpositiveConstants.injective (h.trans (map_zero nonpositiveConstants).symm)
  · rintro ⟨c, rfl, hc⟩
    rw [Polynomial.eval₂_at_apply, hc, map_zero]

/-- Algebraicity over the coefficient field is equivalent to constancy in the support ring. -/
theorem nonpositiveSupport_isAlgebraic_iff (f : nonpositiveSupportSubring Γ K) :
    IsAlgebraic K f ↔ f = nonpositiveConstants (nonpositiveConstantCoeff f) := by
  constructor
  · rintro ⟨P, hP, hroot⟩
    by_contra hf
    exact nonpositiveSupport_eval_ne_zero P hP f hf hroot
  · intro hf
    rw [hf]
    exact isAlgebraic_algebraMap _

/-- Every nonconstant support-ring element is transcendental over its coefficient field. -/
theorem nonpositiveSupport_transcendental_iff (f : nonpositiveSupportSubring Γ K) :
    Transcendental K f ↔ f ≠ nonpositiveConstants (nonpositiveConstantCoeff f) := by
  exact not_congr (nonpositiveSupport_isAlgebraic_iff f)

/-- Roots in an intermediate ring are precisely its ordinary constant roots, even when
that ring is not closed under taking constant coefficients. -/
theorem intermediate_polynomial_root_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (o : Subring K) (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ o)
    (P : Polynomial K) (hP : P ≠ 0) (f : A) :
    P.eval₂ nonpositiveConstants (f : nonpositiveSupportSubring Γ K) = 0 ↔
      ∃ c : o, (f : nonpositiveSupportSubring Γ K) = nonpositiveConstants (c : K) ∧
        P.eval (c : K) = 0 := by
  rw [nonpositiveSupport_polynomial_root_iff P hP]
  constructor
  · rintro ⟨c, hc, hp⟩
    have hm : c ∈ o := (hA c).mp (hc ▸ f.property)
    exact ⟨⟨c, hm⟩, hc, hp⟩
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, hp⟩

/-- A polynomial without roots in the prescribed constant subring has none in the
intermediate Hahn ring. This also handles the zero polynomial via the root at zero. -/
theorem intermediate_polynomial_no_root (A : Subring (nonpositiveSupportSubring Γ K))
    (o : Subring K) (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ o)
    (P : Polynomial K) (hP : ∀ c : o, P.eval (c : K) ≠ 0) (f : A) :
    P.eval₂ nonpositiveConstants (f : nonpositiveSupportSubring Γ K) ≠ 0 := by
  have hp : P ≠ 0 := by
    intro hz
    have h := hP 0
    simp [hz] at h
  intro hf
  obtain ⟨c, _, hc⟩ := (intermediate_polynomial_root_iff A o hA P hp f).mp hf
  exact hP c hc

end
end Surreal.HahnSeries
