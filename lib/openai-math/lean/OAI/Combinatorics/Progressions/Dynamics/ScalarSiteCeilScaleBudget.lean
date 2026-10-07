import OAI.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus

namespace OAI

section

namespace Erdos3.ScalarSiteExpansion
open scoped NNReal Classical
universe u v
variable {S : Type u} [Fintype S]

theorem atCeilScale_exp_bounds (e : ScalarSiteExpansion.{u,v} S) (K d : ℕ)
    {γ D v g A O H : ℝ} (hK : 0 < K) (hγ : 0 < γ)
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hH : 0 ≤ H) (hd : (d : ℝ) ≤ D)
    (hγv : γ ≤ Real.exp v) (hγg : γ⁻¹ ≤ Real.exp g) (hHA : H ≤ Real.exp A)
    (he : e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ H) :
    let O' := O + (D + 1) * (v + 1)
    (e.atCeilScale K d γ).Bounds (Real.exp O') (Real.exp O') (Real.exp O')
      ⟨Real.exp O', Real.exp_nonneg _⟩ (Real.exp (A + g)) := by
  intro O'
  have hg1 : γ + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_comm γ 1] using one_add_le_exp_succ hv hγv
  have hpower : (γ + 1) ^ d ≤ Real.exp (D * (v + 1)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hg1 (by positivity) d hd
  have hO : Real.exp O ≤ Real.exp O' := Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity))
  apply (atCeilScale_bounds e K d hK hγ (Real.exp_nonneg _) hH he).mono hO hO _ _ _
  · have hb := mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg O)
    rw [← Real.exp_add] at hb
    apply hb.trans (Real.exp_le_exp.mpr _)
    dsimp [O']
    nlinarith only [hv]
  · apply NNReal.coe_le_coe.mp
    change Real.exp O * (Real.toNNReal (γ + 1) : ℝ) ≤ Real.exp O'
    rw [Real.coe_toNNReal (γ + 1) (by positivity)]
    have hb := mul_le_mul_of_nonneg_left hg1 (Real.exp_nonneg O)
    rw [← Real.exp_add] at hb
    apply hb.trans (Real.exp_le_exp.mpr _)
    dsimp [O']
    nlinarith only [mul_nonneg hD (show 0 ≤ v + 1 by positivity)]
  · exact (mul_le_mul hHA hγg (inv_nonneg.mpr hγ.le) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm

theorem ceilScaleAccuracy_bounds {γ ε D v E : ℝ} (d : ℕ)
    (hγ : 0 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1) (_hD : 0 ≤ D) (hv : 0 ≤ v)
    (hd : (d : ℝ) ≤ D) (hγv : γ ≤ Real.exp v) (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := ε / (2 * (γ + 1) ^ d)
    0 < ζ ∧ ζ ≤ 1 ∧ ζ⁻¹ ≤ Real.exp (E + D * (v + 1) + 1) ∧
      (γ + 1) ^ d * (2 * ζ) = ε := by
  intro ζ
  have hg1 : 1 ≤ (γ + 1) ^ d := one_le_pow₀ (by linarith only [hγ])
  have hgpos : 0 < (γ + 1) ^ d := by positivity
  have hζpos : 0 < ζ := div_pos hε (by positivity)
  have hζle : ζ ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (γ + 1) ^ d)).mpr
    nlinarith only [hε1, hg1]
  have hγe : γ + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_comm γ 1] using one_add_le_exp_succ hv hγv
  have hp := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ γ + 1) hγe (by positivity) d hd
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨hζpos, hζle, ?_, ?_⟩
  · change (ε / (2 * (γ + 1) ^ d))⁻¹ ≤ _
    rw [inv_div, div_eq_mul_inv]
    have hb := mul_le_mul (mul_le_mul htwo hp (by positivity) (Real.exp_nonneg _))
      hεE (inv_nonneg.mpr hε.le) (by positivity)
    exact hb.trans_eq (by simp only [← Real.exp_add]; congr 1; ring)
  · dsimp [ζ]
    field_simp

end Erdos3.ScalarSiteExpansion

end

end OAI
