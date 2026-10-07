import OAI.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget

namespace OAI

section

namespace Erdos3

theorem slicedEndpointUniformScale_exp_lower (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) ≤
      slicedPolynomialScale N O N m m 1 1 a δ A η := by
  have hpos := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).1
  have hinv := slicedEndpointUniformScale_inverse_le_exp N O m
    ha hδ hA hη hP hN hO hm haP hδP hAP hηP
  have h := one_div_le_one_div_of_le (inv_pos.mpr hpos) hinv
  simpa only [one_div, inv_inv, ← Real.exp_neg] using h

theorem slicedEndpointUniformScale_exp_lower_div (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) ≤
      slicedPrincipalC2Tolerance N O m 1 a δ A η / (1 + polynomialMassC2Budget N m 1) :=
  slicedEndpointUniformScale_exp_lower N O m ha hδ hA hη hP hN hO hm haP hδP hAP hηP

theorem slicedEndpointUniformScale_exp_tail_tolerance (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P)
    (N' O' : ℕ) (hN' : N' ≤ N) (hO' : O' ≤ O) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) *
        polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  have hs := slicedEndpointUniformScale_exp_lower N O m
    ha hδ hA hη hP hN hO hm haP hδP hAP hηP
  have h := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).2.2 N' O' hN' hO'
    (Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)))
    (by simpa only [abs_of_pos (Real.exp_pos _)] using hs)
  simpa only [abs_of_pos (Real.exp_pos _)] using h

end Erdos3

end

end OAI
