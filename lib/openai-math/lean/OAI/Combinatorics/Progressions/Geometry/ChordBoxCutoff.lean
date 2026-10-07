-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.Estimates.LinearCutoff
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def chordBoxCutoff (a : ℝ) (h : ℝ≥0) (z : ι → ℂ) : ℝ :=
  ∏ i, linearCutoff a h ‖1 - z i‖

theorem chordBoxCutoff_range (a : ℝ) (h : ℝ≥0) (z : ι → ℂ) :
    0 ≤ chordBoxCutoff a h z ∧ chordBoxCutoff a h z ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (linearCutoff_range a h _).1),
    Finset.prod_le_one₀ (fun i _ => (linearCutoff_range a h _).1)
      (fun i _ => (linearCutoff_range a h _).2)⟩

theorem chordBoxCutoff_eq_one (a : ℝ) (h : ℝ≥0) (hh : 0 < h)
    (z : ι → ℂ) (hz : ∀ i, ‖1 - z i‖ ≤ a) : chordBoxCutoff a h z = 1 := by
  exact Finset.prod_eq_one (fun i _ => linearCutoff_eq_one a h hh (hz i))

theorem chordBoxCutoff_eq_zero (a : ℝ) (h : ℝ≥0) (z : ι → ℂ)
    (hz : ∃ i, a + (h : ℝ) ≤ ‖1 - z i‖) : chordBoxCutoff a h z = 0 := by
  classical
  obtain ⟨i, hi⟩ := hz
  exact Finset.prod_eq_zero (Finset.mem_univ i) (linearCutoff_eq_zero a h hi)

theorem chordBoxCutoff_mono_center {a b : ℝ} (hab : a ≤ b) (h : ℝ≥0) (z : ι → ℂ) :
    chordBoxCutoff a h z ≤ chordBoxCutoff b h z := by
  exact Finset.prod_le_prod₀ (fun i _ => (linearCutoff_range a h _).1)
    (fun i _ => linearCutoff_mono_center hab h _)

theorem chordBoxCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith (Fintype.card ι * h⁻¹) (chordBoxCutoff (ι := ι) a h) := by
  have hsingle : LipschitzWith h⁻¹ (fun z : ℂ => linearCutoff a h ‖1 - z‖) := by
    simpa only [Function.comp_def, mul_one, dist_eq_norm] using
      (linearCutoff_lipschitz a h hh).comp (LipschitzWith.dist_right (1 : ℂ))
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hcoord (i : ι) :
      |linearCutoff a h ‖1 - z i‖ - linearCutoff a h ‖1 - w i‖| ≤
        (h⁻¹ : ℝ≥0) * dist z w := by
    have hi := hsingle.dist_le_mul (z i) (w i)
    rw [Real.dist_eq] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist z w i) (by positivity))
  have hprod := abs_finset_prod_sub_prod_le Finset.univ
    (fun i => linearCutoff a h ‖1 - z i‖) (fun i => linearCutoff a h ‖1 - w i‖)
    (B := 1) (δ := (h⁻¹ : ℝ≥0) * dist z w) le_rfl (by positivity)
    (fun i _ => by rw [abs_of_nonneg (linearCutoff_range a h _).1]; exact (linearCutoff_range a h _).2)
    (fun i _ => by rw [abs_of_nonneg (linearCutoff_range a h _).1]; exact (linearCutoff_range a h _).2)
    (fun i _ => hcoord i)
  rw [Real.dist_eq]
  apply hprod.trans_eq
  simp only [Finset.card_univ, one_pow, mul_one, NNReal.coe_mul, NNReal.coe_natCast]
  ring

end Erdos3

end

end OAI
