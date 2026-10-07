import OAI.Combinatorics.Progressions.Fourier.AllocatedErrorStandardFourier
import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientSiteCoordinates
import OAI.Combinatorics.Progressions.Probability.AllocatedProbabilityMajorantMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedProfileErrorCap (A Cf Cg : ℝ≥0) (V : Fin m → ℝ≥0) : ℝ≥0 :=
  allocatedErrorKernelCap B U b S (O := O) 1 A V * (Cf + Cg)

noncomputable def allocatedProfileErrorLip (A Cf Cg Kf Kg : ℝ≥0) (C V : Fin m → ℝ≥0) : ℝ≥0 :=
  allocatedErrorKernelCap B U b S (O := O) 1 A V *
      ((Kf + Kg) * (∑ j, C j * Fintype.card (J j))) +
    (Cf + Cg) * allocatedErrorKernelLip B U b S (O := O) 1 A C V

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedProfileErrorAmbientKernel (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) (z : JetAmbientIndex O J → ℝ) : ℝ :=
  allocatedErrorAmbientKernel B U b S o hR hσ x u v rows 1 A z *
    |f (allocatedLongAmbientCoordinates B U b S o z) - g (allocatedLongAmbientCoordinates B U b S o z)|

theorem allocatedProfileErrorAmbientKernel_support (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) (z : JetAmbientIndex O J → ℝ)
    (hz : allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g z ≠ 0) :
    ∀ i, |z i| < 1 / 2 := by
  apply allocatedErrorAmbientKernel_support B U b S o hR hσ x u v rows 1 A z
  intro he
  exact hz (by simp only [allocatedProfileErrorAmbientKernel, he, zero_mul])

theorem allocatedProfileErrorAmbientKernel_bounds (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    (∀ z, 0 ≤ allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g z ∧
      allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g z ≤
        allocatedProfileErrorCap B U b S (O := O) A Cf Cg V) ∧
    LipschitzWith (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V)
      (allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g) := by
  have hb := allocatedErrorAmbientKernel_bounds B U b S o hR hσ x u v rows 1 A C V hC hV
  have hd : LipschitzWith ((Kf + Kg) * (∑ j, C j * Fintype.card (J j)))
      (fun z => |f (allocatedLongAmbientCoordinates B U b S o z) -
        g (allocatedLongAmbientCoordinates B U b S o z)|) := by
    simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, one_mul] using
      ((lipschitzWith_one_norm.comp (hf.sub hg)).comp (allocatedLongAmbientCoordinates_lipschitz B U b S o C hC))
  have hdb (z : output → ℝ) : |f z - g z| ≤ (Cf + Cg : ℝ≥0) :=
    (abs_sub (f z) (g z)).trans (add_le_add (hfb z) (hgb z))
  refine ⟨fun z => ⟨mul_nonneg (hb.1 z).1 (abs_nonneg _), ?_⟩, ?_⟩
  · exact mul_le_mul (hb.1 z).2 (hdb _) (abs_nonneg _) (NNReal.coe_nonneg _)
  · exact lipschitz_real_mul_of_bounds _ _ hb.2 hd
      (fun z => by rw [abs_of_nonneg (hb.1 z).1]; exact (hb.1 z).2)
      (fun z => by rw [abs_abs]; exact hdb _)

noncomputable def allocatedProfileErrorTorusKernel (A : ℝ≥0) (f g : (output → ℝ) → ℝ) :
    (JetAmbientIndex O J → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g)

noncomputable def allocatedProfileErrorMajorant (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (d : ℕ) (y : EuclideanJetLayers U O) : ℝ :=
  allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g (coveredJetAmbientTorus U d y)

theorem allocatedProfileErrorTorusKernel_bounds (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    (∀ z, 0 ≤ allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g z ∧
      allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g z ≤
        allocatedProfileErrorCap B U b S (O := O) A Cf Cg V) ∧
    LipschitzWith (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V)
      (allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g) := by
  have h := allocatedProfileErrorAmbientKernel_bounds B U b S o hR hσ x u v rows A f g hf hg hfb hgb C V hC hV
  exact ⟨smallBoxTorusKernel_range _ (NNReal.coe_nonneg _) h.1
      (allocatedProfileErrorAmbientKernel_support B U b S o hR hσ x u v rows A f g),
    smallBoxTorusKernel_lipschitz _ h.2 (fun z => (h.1 z).1)
      (allocatedProfileErrorAmbientKernel_support B U b S o hR hσ x u v rows A f g)⟩

theorem exists_allocated_profile_error_fourier (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ P)
    (hLip : (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → JetAmbientIndex O J → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        allocatedProfileErrorCap B U b S (O := O) A Cf Cg V ∧
      ∀ y, ‖(allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g y : ℂ) -
        ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • y i)‖ ≤ δ := by
  have h := allocatedProfileErrorTorusKernel_bounds B U b S o hR hσ x u v rows A f g hf hg hfb hgb C V hC hV
  have hl : LipschitzWith (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V)
      (fun y => (allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g y : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Complex.isometry_ofReal.dist_eq]
    exact h.2.dist_le_mul y z
  exact exists_ambient_torus_fourier_approximation _ _ _ hl
    (fun y => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.1 y).1] using (h.1 y).2)
    hδ hP hdim hLip hδP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

noncomputable def allocatedProbabilityProfileAmbientKernel (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) (z : JetAmbientIndex O J → ℝ) : ℝ :=
  allocatedProbabilityAmbientKernel B U b S o p 1 A z *
    |f (allocatedLongAmbientCoordinates B U b S o z) - g (allocatedLongAmbientCoordinates B U b S o z)|

theorem allocatedProbabilityProfileAmbientKernel_support (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) (z : JetAmbientIndex O J → ℝ)
    (hz : allocatedProbabilityProfileAmbientKernel B U b S o p A f g z ≠ 0) :
    ∀ i, |z i| < 1 / 2 := by
  apply allocatedProbabilityAmbientKernel_support B U b S o p 1 A z
  intro he
  exact hz (by simp only [allocatedProbabilityProfileAmbientKernel, he, zero_mul])

theorem allocatedProbabilityProfileAmbientKernel_bounds (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    (∀ z, 0 ≤ allocatedProbabilityProfileAmbientKernel B U b S o p A f g z ∧
      allocatedProbabilityProfileAmbientKernel B U b S o p A f g z ≤
        allocatedProfileErrorCap B U b S (O := O) A Cf Cg V) ∧
    LipschitzWith (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V)
      (allocatedProbabilityProfileAmbientKernel B U b S o p A f g) := by
  have hb := allocatedProbabilityAmbientKernel_bounds B U b S o p 1 A C V hC hV
  have hd : LipschitzWith ((Kf + Kg) * (∑ j, C j * Fintype.card (J j)))
      (fun z => |f (allocatedLongAmbientCoordinates B U b S o z) -
        g (allocatedLongAmbientCoordinates B U b S o z)|) := by
    simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, one_mul] using
      ((lipschitzWith_one_norm.comp (hf.sub hg)).comp (allocatedLongAmbientCoordinates_lipschitz B U b S o C hC))
  have hdb (z : output → ℝ) : |f z - g z| ≤ (Cf + Cg : ℝ≥0) :=
    (abs_sub (f z) (g z)).trans (add_le_add (hfb z) (hgb z))
  refine ⟨fun z => ⟨mul_nonneg (hb.1 z).1 (abs_nonneg _), ?_⟩, ?_⟩
  · exact mul_le_mul (hb.1 z).2 (hdb _) (abs_nonneg _) (NNReal.coe_nonneg _)
  · exact lipschitz_real_mul_of_bounds _ _ hb.2 hd
      (fun z => by rw [abs_of_nonneg (hb.1 z).1]; exact (hb.1 z).2)
      (fun z => by rw [abs_abs]; exact hdb _)

noncomputable def allocatedProbabilityProfileTorusKernel (A : ℝ≥0) (f g : (output → ℝ) → ℝ) :
    (JetAmbientIndex O J → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedProbabilityProfileAmbientKernel B U b S o p A f g)

noncomputable def allocatedProbabilityProfileMajorant (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (d : ℕ) (y : EuclideanJetLayers U O) : ℝ :=
  allocatedProbabilityProfileTorusKernel B U b S o p A f g (coveredJetAmbientTorus U d y)

theorem allocatedProbabilityProfileTorusKernel_bounds (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    (∀ z, 0 ≤ allocatedProbabilityProfileTorusKernel B U b S o p A f g z ∧
      allocatedProbabilityProfileTorusKernel B U b S o p A f g z ≤
        allocatedProfileErrorCap B U b S (O := O) A Cf Cg V) ∧
    LipschitzWith (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V)
      (allocatedProbabilityProfileTorusKernel B U b S o p A f g) := by
  have h := allocatedProbabilityProfileAmbientKernel_bounds B U b S o p A f g hf hg hfb hgb C V hC hV
  exact ⟨smallBoxTorusKernel_range _ (NNReal.coe_nonneg _) h.1
      (allocatedProbabilityProfileAmbientKernel_support B U b S o p A f g),
    smallBoxTorusKernel_lipschitz _ h.2 (fun z => (h.1 z).1)
      (allocatedProbabilityProfileAmbientKernel_support B U b S o p A f g)⟩

theorem exists_allocated_probability_profile_fourier (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ P)
    (hLip : (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → JetAmbientIndex O J → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        allocatedProfileErrorCap B U b S (O := O) A Cf Cg V ∧
      ∀ y, ‖(allocatedProbabilityProfileTorusKernel B U b S o p A f g y : ℂ) -
        ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • y i)‖ ≤ δ := by
  have h := allocatedProbabilityProfileTorusKernel_bounds B U b S o p A f g hf hg hfb hgb C V hC hV
  have hl : LipschitzWith (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V)
      (fun y => (allocatedProbabilityProfileTorusKernel B U b S o p A f g y : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Complex.isometry_ofReal.dist_eq]
    exact h.2.dist_le_mul y z
  exact exists_ambient_torus_fourier_approximation _ _ _ hl
    (fun y => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.1 y).1] using (h.1 y).2)
    hδ hP hdim hLip hδP

end Erdos3.VectorPolynomial

end

end OAI
