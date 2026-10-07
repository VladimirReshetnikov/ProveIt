import OAI.Combinatorics.Progressions.Probability.OneCubeSlicedSourceLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]

theorem oneCubeSlicedParameter_norm_le
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)
    (hw : ∀ d p, |lower d p| + |width d p| ≤ 1)
    (x : OneCubeActiveEndpoint (B := B) h P → ℝ) (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) :
    ‖oneCubeSlicedParameter h P lower width x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  rcases j with ⟨d,b,i,r⟩
  have hx₀ := hx ⟨(false,d),b,i⟩
  have hx₁ := hx ⟨(true,d),b,i⟩
  have hxabs : |x ⟨(false,d),b,i⟩| ≤ 1 := by rw [abs_of_nonneg hx₀.1]; exact hx₀.2
  have hdiff : |x ⟨(true,d),b,i⟩ - x ⟨(false,d),b,i⟩| ≤ 1 := abs_le.mpr ⟨by linarith [hx₀.2, hx₁.1], by linarith [hx₀.1, hx₁.2]⟩
  cases r with
  | none =>
    simp only [oneCubeSlicedParameter, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans ((add_le_add le_rfl
      (by simpa only [abs_mul, mul_one] using mul_le_mul_of_nonneg_left hxabs (abs_nonneg (width d (b,i))))).trans (hw d (b,i)))
  | some r =>
    simp only [oneCubeSlicedParameter, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)).trans (by linarith [hw d (b,i), abs_nonneg (lower d (b,i))])

theorem oneCubeSlicedParameter_ae_norm_le
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)
    (hw : ∀ d p, |lower d p| + |width d p| ≤ 1) :
    ∀ᵐ x ∂unitBoxMeasure (OneCubeActiveEndpoint (B := B) h P),
      ‖oneCubeSlicedParameter h P lower width x‖ ≤ 1 := by
  filter_upwards [unitBoxMeasure_ae] with x hx
  exact oneCubeSlicedParameter_norm_le h P lower width hw x (fun j => ⟨(hx j).1.le, (hx j).2⟩)

end Erdos3

end

end OAI
