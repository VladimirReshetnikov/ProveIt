import Surreal.Surcomplex.TrigonometricOrder
import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# The defect and sine valuation of an actual interior angle

The defect is the smaller of an angle and its supplement. Jordan's
inequality gives an ordinary-factor comparison between this defect and
the sine, proving the first assertion of `trigonometry:thm:valuationtriangle`
and `trigonometry:eq:valuationtriangle` at every finite actual angle in
the interior range, including infinitesimal distances from either endpoint.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Distance from the nearer endpoint of the actual interior-angle interval. -/
def angleDefect (θ : SignSequence.FiniteElement.{u}) : SignSequence.FiniteElement.{u} :=
  min θ (SignSequence.finiteOfReal Real.pi - θ)

@[simp] theorem val_angleDefect (θ : SignSequence.FiniteElement.{u}) :
    (angleDefect θ).val = min θ.val (SignSequence.ofReal Real.pi - θ.val) := rfl

/-- The defect of an interior angle belongs to the positive closed quarter-period. -/
theorem angleDefect_mem (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) :
    (angleDefect θ).val ∈ Set.Ioc 0 (SignSequence.ofReal (Real.pi / 2)) := by
  rw [val_angleDefect, map_div₀, map_ofNat]
  refine ⟨lt_min hθ.1 (sub_pos.mpr hθ.2), ?_⟩
  have h₁ := min_le_left θ.val (SignSequence.ofReal Real.pi - θ.val)
  have h₂ := min_le_right θ.val (SignSequence.ofReal Real.pi - θ.val)
  linarith only [h₁, h₂]

/-- Supplementary actual angles have the same defect. -/
theorem angleDefect_supplement (θ : SignSequence.FiniteElement.{u}) :
    angleDefect (SignSequence.finiteOfReal Real.pi - θ) = angleDefect θ := by
  simp only [angleDefect, sub_sub_cancel, min_comm]

/-- Passing from an angle to its defect preserves its actual sine. -/
theorem finiteSin_angleDefect (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (angleDefect θ) = finiteSin θ := by
  unfold angleDefect
  rcases le_total θ (SignSequence.finiteOfReal Real.pi - θ) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, finiteSin_sub]
    simp only [finiteSin_constant, finiteCos_constant, Real.sin_pi, Real.cos_pi,
      map_zero, map_neg, map_one, zero_mul, neg_one_mul, zero_sub, neg_neg]

/-- Jordan's bounds compare sine to the defect by fixed nonzero ordinary factors. -/
theorem angleDefect_sine_bounds (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) :
    finiteSin θ ≤ (angleDefect θ).val ∧
      (angleDefect θ).val ≤ SignSequence.ofReal (Real.pi / 2) * finiteSin θ := by
  have hd := angleDefect_mem θ hθ
  have hj := finiteSin_jordan (angleDefect θ) ⟨hd.1.le, hd.2⟩
  rw [finiteSin_angleDefect] at hj
  refine ⟨hj.2, ?_⟩
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hl := (div_le_iff₀ hp).mp hj.1
  rw [map_div₀, map_ofNat]
  linarith only [hl]

/-- Sine has exactly the valuation of the distance from the nearer angle endpoint. -/
theorem valuation_finiteSin_eq_angleDefect (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) :
    SignSequence.valuation (finiteSin θ) = SignSequence.valuation (angleDefect θ).val := by
  obtain ⟨hlo, hhi⟩ := angleDefect_sine_bounds θ hθ
  apply le_antisymm
  · have h := SignSequence.valuation_antitone_nonneg (angleDefect_mem θ hθ).1.le hhi
    rw [SignSequence.valuation_mul,
      SignSequence.valuation_ofReal_of_ne_zero (half_pos Real.pi_pos).ne', zero_add] at h
    exact h
  · exact SignSequence.valuation_antitone_nonneg (finiteSin_pos_of_mem_Ioo θ hθ).le hlo

end
end Surreal.Surcomplex
