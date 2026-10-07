import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradedCoefficientBound
import OAI.Combinatorics.Progressions.Probability.AllocatedRecoveredChartMass

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] {I E : Fin m → Type*} {J : Fin m → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_pulled_slow
    [Fintype X]
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (basis '' {i | j ≤ ω i}))
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {budget : ℝ} (hcontrol : NilpotentLieFiltration.FullChartControlledFactors F basis ω hF J poly N left right budget)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)

    : F.SymbolSlowBound basis ω hF (fun _ : LayerSamplerVariables G I n B => 1)
      (layerSamplerBox B U b S)
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
      (F.realSymbolHomogeneousPullbackHom basis ω hF (fullTaggedVariableWeight (X := X) J)
        (fun _ : LayerSamplerVariables G I n B => 1)
        (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
          (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) left) := by
  apply NilpotentLieFiltration.FullChartControlledFactors.homogeneousPullback_slow
    F basis ω hF J poly N left right hcontrol
  · intro k
    exact lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  · have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    simpa only [one_mul] using
      mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  · exact h.integerFullChart_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_pulled_slow
    [Fintype X]
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (basis '' {i | j ≤ ω i}))
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {budget : ℝ} (hcontrol : NilpotentLieFiltration.FullChartControlledFactors F basis ω hF J poly N left right budget)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)

    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    : F.SymbolSlowBound basis ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
      (F.realSymbolHomogeneousPullbackHom basis ω hF (fullTaggedVariableWeight (X := X) J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
          (integerSampledRealChart (fun z => freezePolynomial keep fixed
            (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) left) := by
  apply NilpotentLieFiltration.FullChartControlledFactors.homogeneousPullback_slow
    F basis ω hF J poly N left right hcontrol
  · intro k
    exact lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k.val)
  · have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    simpa only [one_mul] using
      mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  · exact h.integerFullChart_frozen_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall keep fixed

end Erdos3.VectorPolynomial

end

end OAI
