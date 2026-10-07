/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedErrorInterpolation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedErrorAmbientKernel (η A : ℝ≥0) (z : JetAmbientIndex O J → ℝ) : ℝ :=
  (η : ℝ) * A *
    (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)) *
    (smallBoxCutoff z * allocatedGridJetInterpolation B U b S hR hσ x u v rows
      (allocatedGridAmbientCoordinates B U b S o z))

theorem allocatedErrorAmbientKernel_support (η A : ℝ≥0) (z : JetAmbientIndex O J → ℝ)
    (hz : allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A z ≠ 0) :
    ∀ i, |z i| < 1 / 2 := by
  apply smallBoxCutoff_support z
  intro he
  exact hz (by simp only [allocatedErrorAmbientKernel, he, zero_mul, mul_zero])

theorem allocatedErrorAmbientKernel_quarter (η A : ℝ≥0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (hz : ∀ i, |mixedJetAmbientPoint U b o z i| ≤ 1 / 4) :
    allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A (mixedJetAmbientPoint U b o z) =
      (η : ℝ) * A *
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)) *
      allocatedGridJetInterpolation B U b S hR hσ x u v rows
        (allocatedGridNormalizedRows B U b S (fun a => coefficientJetAxisEquiv O I n z a.val)) := by
  rw [allocatedErrorAmbientKernel, smallBoxCutoff_one _ hz, one_mul,
    allocatedGridAmbientCoordinates_point]

theorem allocatedErrorAmbientKernel_bounds (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    let N := Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}
    let M : ℝ≥0 := (K ^ D) ^ N
    let L : ℝ≥0 := N * (D * (2 * K ^ 2) * K ^ D) * M
    let W : ℝ≥0 := η * A * ∏ j, V j ^ Fintype.card (O j)
    (∀ z, 0 ≤ allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A z ∧
      allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A z ≤ W * M) ∧
    LipschitzWith (W * (L * (∑ j, C j * Fintype.card (J j)) + M * 8))
      (allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A) := by
  intro K D N M L W
  let F := allocatedGridJetInterpolation B U b S hR hσ x u v rows
  let c : ℝ := (η : ℝ) * A *
    ∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg η.coe_nonneg A.coe_nonneg)
    (Finset.prod_nonneg (fun j _ => pow_nonneg (hV j).1 _))
  have hc : c ≤ W := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg η.coe_nonneg A.coe_nonneg)
    exact_mod_cast Finset.prod_le_prod₀ (fun j _ => pow_nonneg (hV j).1 _)
      (fun j _ => pow_le_pow_left₀ (hV j).1 (hV j).2 _)
  have hf := allocatedGridJetInterpolation_uniform_bounds B U b S hR hσ x u v rows
  have hf0 (z) : 0 ≤ F z := (hf.1 z).1
  have hfcap (z) : |F z| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (hf0 z)]
    simpa only [M, K, D, N, NNReal.coe_pow] using (hf.1 z).2
  have hfl : LipschitzWith (L * (∑ j, C j * Fintype.card (J j)))
      (fun z => F (allocatedGridAmbientCoordinates B U b S o z)) :=
    hf.2.comp (allocatedGridAmbientCoordinates_lipschitz B U b S o C hC)
  have hcut := smallBoxCutoff_mul_lipschitz _ hfl
    (fun z => hfcap (allocatedGridAmbientCoordinates B U b S o z))
  have hcut0 (z : JetAmbientIndex O J → ℝ) :
      0 ≤ smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z) :=
    mul_nonneg (smallBoxCutoff_range z).1 (hf0 _)
  have hcutcap (z : JetAmbientIndex O J → ℝ) :
      |smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z)| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (hcut0 z)]
    exact (mul_le_mul_of_nonneg_right (smallBoxCutoff_range z).2 (hf0 _)).trans
      (by simpa only [one_mul, abs_of_nonneg (hf0 _)] using hfcap (allocatedGridAmbientCoordinates B U b S o z))
  refine ⟨fun z => ⟨mul_nonneg hc0 (hcut0 z), ?_⟩, ?_⟩
  · change c * (smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z)) ≤
      (W : ℝ) * (M : ℝ)
    exact mul_le_mul hc ((le_abs_self _).trans (hcutcap z)) (hcut0 z) W.coe_nonneg
  · have h := lipschitz_real_mul_of_bounds (Bf := W) (Bg := M) (fun _ => c)
      (fun z => smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z))
      (LipschitzWith.const c) hcut (fun _ => by rwa [abs_of_nonneg hc0]) hcutcap
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (c * (smallBoxCutoff z * F (allocatedGridAmbientCoordinates B U b S o z)))
      (c * (smallBoxCutoff w * F (allocatedGridAmbientCoordinates B U b S o w))) ≤ _
    have hh := h.dist_le_mul z w
    simpa only [mul_zero, add_zero] using hh

end Erdos3.VectorPolynomial

end

end OAI
