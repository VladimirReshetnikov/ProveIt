import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def joinedCoefficientProfile {J N : Type*}
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (x : J ⊕ N → ℝ) : ℝ :=
  f (fun j => x (.inl j)) * g (fun n => x (.inr n))

theorem joinedCoefficientProfile_nonneg {J N : Type*}
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) (x) :
    0 ≤ joinedCoefficientProfile f g x := mul_nonneg (hf _) (hg _)

theorem joinedCoefficientProfile_lipschitz {J N : Type*} [Fintype J] [Fintype N]
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (H Q K L : ℝ≥0)
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfr : ∀ x, f x ∈ Set.Icc (0 : ℝ) H) (hgr : ∀ y, g y ∈ Set.Icc (0 : ℝ) Q) :
    LipschitzWith (Q*K+H*L) (joinedCoefficientProfile f g) :=
  splitInputProfile_lipschitz (binaryDensity_lipschitz f g H Q K L hfr hgr hf hg)

theorem joinedCoefficientProfile_zero_outside {J N : Type*} [Fintype J] [Fintype N]
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ y, S < ‖y‖ → g y = 0) :
    ∀ x, max R S < ‖x‖ → joinedCoefficientProfile f g x = 0 := by
  intro x hx
  rw [← splitCoordinates_norm x, Prod.norm_def] at hx
  rcases lt_max_iff.mp hx with h | h
  · exact mul_eq_zero_of_left (hfs _ ((le_max_left R S).trans_lt h)) _
  · exact mul_eq_zero_of_right _ (hgs _ ((le_max_right R S).trans_lt h))

theorem joinedCoefficientProfile_integrable {J N : Type*} [Fintype J] [Fintype N]
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (joinedCoefficientProfile f g) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).integrable_comp_of_integrable
    (binaryDensity_integrable hf hg)

theorem joinedCoefficientProfile_measure {J N : Type*} [Fintype J] [Fintype N]
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) :
    ((realDensityMeasure volume f).prod (realDensityMeasure volume g)).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm =
      realDensityMeasure volume (joinedCoefficientProfile f g) := by
  rw [binaryDensity_measure volume volume f g hf hg hf0,
    ← Measure.volume_eq_prod,
    realDensityMeasure_map_equiv,
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : J ⊕ N => ℝ)).map_eq]
  rfl

theorem affineProductProfile_joined {J N : Type*} [Fintype J] [Fintype N]
    (c w : J ⊕ N → ℝ) :
    affineProductProfile c w = joinedCoefficientProfile
      (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))
      (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))) := by
  funext x
  simp only [affineProductProfile, joinedCoefficientProfile, Fintype.prod_sum_type]

end Erdos3

end

end OAI
