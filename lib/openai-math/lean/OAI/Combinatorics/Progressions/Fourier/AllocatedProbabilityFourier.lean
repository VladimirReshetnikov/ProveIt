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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (laws : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

theorem exists_allocated_probability_fourier (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ P)
    (hLip : (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → JetAmbientIndex O J → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        allocatedErrorKernelCap B U b S (O := O) η A V ∧
      ∀ y, ‖(allocatedProbabilityTorusKernel B U b S o laws η A y : ℂ) -
        ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • y i)‖ ≤ δ := by
  have h := allocatedProbabilityTorusKernel_bounds B U b S o laws η A C V hC hV
  have hl : LipschitzWith (allocatedErrorKernelLip B U b S (O := O) η A C V)
      (fun y => (allocatedProbabilityTorusKernel B U b S o laws η A y : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Complex.isometry_ofReal.dist_eq]
    exact h.2.dist_le_mul y z
  exact exists_ambient_torus_fourier_approximation _ _ _ hl
    (fun y => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.1 y).1] using (h.1 y).2)
    hδ hP hdim hLip hδP

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin q) ((j : ℕ) + 1))

variable (laws : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
  PMF (CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) a.val))

theorem exists_allocated_probability_standard_fourier (d : ℕ) (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ P)
    (hLip : (allocatedErrorKernelLip B U b S (O := jets) η A C V : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a j e, e.degree ≤ j.val + 1 → ∀ i,
        |(frequency a j e i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4) * d) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        allocatedErrorKernelCap B U b S (O := jets) η A V ∧
      ∀ y, ‖(allocatedProbabilityMajorant B U b S o laws η A d
        (standardPhysicalJetMap U y) : ℂ) - coefficientTorusFourierSum U frequency c y‖ ≤ δ := by
  obtain ⟨F, inst, frequency, c, hcard, hfreq, hsum, herr⟩ :=
    exists_allocated_probability_fourier B U b S o laws η A C V hC hV hδ hP hdim hLip hδP
  let _ := inst
  refine ⟨F, inst, fun a => standardJetFrequency d (frequency a), c, hcard, ?_, hsum, ?_⟩
  · intro a j e he i
    exact standardJetFrequency_bound d (frequency a) (hfreq a) j e he i
  · intro y
    change ‖(allocatedProbabilityTorusKernel B U b S o laws η A
      (coveredJetAmbientTorus U d (standardPhysicalJetMap U y)) : ℂ) -
        ∑ a, c a * coefficientTorusCharacter U (standardJetFrequency d (frequency a)) y‖ ≤ δ
    simpa only [standardJetFrequency_character] using
      herr (coveredJetAmbientTorus U d (standardPhysicalJetMap U y))

end Erdos3.BooleanCubeKernel

end

end OAI
