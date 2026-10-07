import OAI.Combinatorics.Progressions.Sampling.SmoothSplitSampling

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem rectangular_profile_mass_lower {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hintegral : (∫ x, f x) = 1)
    (hsmall : (2 * R + 2) ^ Fintype.card I * L * δ ≤ 1 / 2) :
    (∏ i, S i) / 2 ≤ ∑' k, rectangularWeight f a S k := by
  have he := rectangularLattice_quadrature f hf a S hS hR hδ hδ1 hmesh hsupport
  rw [hintegral] at he
  have hp : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => hS i)
  have hnorm : (1 / 2 : ℝ) ≤ (∑' k, rectangularWeight f a S k) / ∏ i, S i := by
    have hh := (abs_le.mp he).1
    change -((2 * R + 2) ^ Fintype.card I * L * δ) ≤
      (∑' k, rectangularWeight f a S k) / (∏ i, S i) - 1 at hh
    linarith
  have h := (le_div_iff₀ hp).mp hnorm
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def shiftedSmoothProductMass {I : Type*} [Fintype I]
    (a S : I → ℝ) : ℝ := ∑' x, rectangularWeight (smoothProductProfile I) a S x

theorem shiftedSmoothProductMass_eq_prod {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    shiftedSmoothProductMass a S = ∏ i, shiftedSmoothSampleSum (a i) (S i) :=
  shiftedSmoothProductSamples_sum a S hS

theorem shiftedSmoothProductMass_lower {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2) :
    (∏ i, S i) / 2 ≤ shiftedSmoothProductMass a S := by
  apply rectangular_profile_mass_lower (smoothProductProfile I) (smoothProductProfile_lipschitz I)
    a S hS zero_le_one hδ hδ1 hmesh (smoothProductProfile_zero_outside I)
    (smoothProductProfile_integral I)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, show 2 * (1 : ℝ) + 2 = 4 by norm_num] using hsmall

noncomputable def shiftedSmoothProductPMF {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) : PMF (I → ℤ) :=
  realWeightPMF (rectangularWeight (smoothProductProfile I) a S)
    (fun _ => (smoothProductProfile_range I _).1)
    (rectangularWeight_summable _ a S hS (smoothProductProfile_zero_outside I)) hZ

theorem shiftedSmoothProductPMF_toReal {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) (x : I → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ x).toReal =
      rectangularWeight (smoothProductProfile I) a S x / shiftedSmoothProductMass a S :=
  realWeightPMF_apply _ _ _ _ x

theorem shiftedSmoothProductPMF_toReal_sum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    (∑' x, (shiftedSmoothProductPMF a S hS hZ x).toReal) = 1 := by
  simp only [shiftedSmoothProductPMF_toReal, tsum_div_const]
  exact div_self hZ.ne'

theorem shiftedSmoothProductPMF_toReal_zero_off {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (x : I → ℤ) (hx : x ∉ rectangularWeightIndices a S 1) :
    (shiftedSmoothProductPMF a S hS hZ x).toReal = 0 := by
  rw [shiftedSmoothProductPMF_toReal,
    rectangularWeight_zero_off_indices _ a S hS (smoothProductProfile_zero_outside I) x hx,
    zero_div]

end Erdos3

end

end OAI
