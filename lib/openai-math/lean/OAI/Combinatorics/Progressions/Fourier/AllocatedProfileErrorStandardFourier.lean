import OAI.Combinatorics.Progressions.Linear.AllocatedProbabilityProfileKernel

namespace OAI

section

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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j : Fin m, BoundedBooleanJet (Fin q) (j.val + 1) → Finset α)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin q) ((j : ℕ) + 1))

local notation "output" => (Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets (Sigma.fst (Subtype.val a)))

theorem exists_allocated_profile_error_standard_fourier (d : ℕ) (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) {Cf Cg Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ P)
    (hLip : (allocatedProfileErrorLip B U b S (O := jets) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a j e, e.degree ≤ j.val + 1 → ∀ i,
        |(frequency a j e i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4) * d) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        allocatedProfileErrorCap B U b S (O := jets) A Cf Cg V ∧
      ∀ y, ‖(allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d
        (standardPhysicalJetMap U y) : ℂ) - coefficientTorusFourierSum U frequency c y‖ ≤ δ := by
  obtain ⟨F, inst, frequency, c, hcard, hfreq, hsum, herr⟩ :=
    exists_allocated_profile_error_fourier B U b S o hR hσ x u v rows A f g hf hg hfb hgb C V hC hV hδ hP hdim hLip hδP
  let _ : Fintype F := inst
  refine ⟨F, inst, fun a => standardJetFrequency d (frequency a), c, hcard, ?_, hsum, ?_⟩
  · intro a j e he i
    exact standardJetFrequency_bound d (frequency a) (hfreq a) j e he i
  · intro y
    change ‖(allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g
      (coveredJetAmbientTorus U d (standardPhysicalJetMap U y)) : ℂ) -
        ∑ a, c a * coefficientTorusCharacter U (standardJetFrequency d (frequency a)) y‖ ≤ δ
    simpa only [standardJetFrequency_character] using
      herr (coveredJetAmbientTorus U d (standardPhysicalJetMap U y))

theorem allocatedProfileErrorMajorant_sample {X : Type*} (A : ℝ≥0)
    (f g : (output → ℝ) → ℝ) (d : ℕ) [NeZero d]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : X → (Unit ⊕ Fin q) → ℤ) :
    allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d
        (physicalCubeEuclideanSample U d p hm z) =
      allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g 1
        (physicalCubeEuclideanSample U 1 p hm z) := by
  unfold allocatedProfileErrorMajorant
  rw [coveredJetAmbientTorus_sample]

end Erdos3.BooleanCubeKernel

end

end OAI
