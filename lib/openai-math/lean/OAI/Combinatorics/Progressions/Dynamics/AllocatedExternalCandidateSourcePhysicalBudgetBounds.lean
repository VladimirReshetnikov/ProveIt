import OAI.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
import OAI.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped TensorProduct

noncomputable def candidateSourceBackendPolynomial (s : ℕ) : Polynomial ℕ :=
  (allocatedAffineCanonicalBackendPolynomial s).comp ((Polynomial.X + 4) ^ 10)

theorem candidateSourceBackendPolynomial_eval (s : ℕ) (pFull : ℝ) :
    (candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) pFull =
      (allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ)
        (candidatePhysicalOrdinaryBudget pFull) := by
  simp only [candidateSourceBackendPolynomial, Polynomial.eval₂_comp,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, candidatePhysicalOrdinaryBudget]

theorem candidateSourceBackendPolynomial_bounds (s : ℕ) {pFull : ℝ} (hp : 0 ≤ pFull) :
    AllocatedAffineCanonicalBackendBounds s (candidatePhysicalOrdinaryBudget pFull) pFull
      ((candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) pFull) := by
  rw [candidateSourceBackendPolynomial_eval]
  have hb := candidatePhysicalOrdinaryBudget_bounds hp
  exact allocatedAffineCanonicalBackendPolynomial_bounds s hb.1 hp le_rfl hb.2.1

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

noncomputable def physicalBudget : ℝ :=
  nativePhysicalTerminalFullBudget (s + 1) m source.Cprimitive source.scheduleExponent source.x

noncomputable def ordinaryBudget : ℝ := candidatePhysicalOrdinaryBudget source.physicalBudget

noncomputable def recursiveParameter : ℝ :=
  finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
    (allocatedAffineCanonicalBudget s source.ordinaryBudget source.physicalBudget)

noncomputable def separation : ℝ :=
  Real.exp (candidatePrimitiveFreezingCutoff s 1
    (allocatedAffineCanonicalBudget s source.ordinaryBudget source.physicalBudget))

theorem physicalBudget_nonneg : 0 ≤ source.physicalBudget :=
  (nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive source.scheduleExponent
    source.x_nonneg).2.2

theorem ordinaryBudget_nonneg : 0 ≤ source.ordinaryBudget :=
  (candidatePhysicalOrdinaryBudget_bounds source.physicalBudget_nonneg).1

theorem recursiveParameter_nonneg : 0 ≤ source.recursiveParameter := by
  have h := (allocatedAffineCanonicalBudget_bounds s source.ordinaryBudget_nonneg
    source.physicalBudget_nonneg).nonnegative
  unfold recursiveParameter finiteFreezingRecursiveParameter
  positivity

theorem physicalBudget_le_recursiveParameter : source.physicalBudget ≤ source.recursiveParameter := by
  have hb := candidatePhysicalOrdinaryBudget_bounds source.physicalBudget_nonneg
  have hc := allocatedAffineCanonicalBudget_bounds s hb.1 source.physicalBudget_nonneg
  change AllocatedAffineCanonicalBudgetBounds s source.ordinaryBudget source.physicalBudget at hc
  have hi := candidatePrimitivePhysical_input_budget s 1 hc.nonnegative
  have hpower : 0 ≤ (allocatedAffineCanonicalBudget s source.ordinaryBudget source.physicalBudget +
      candidatePrimitivePhysicalBudgetExponent s 1) ^ candidatePrimitivePhysicalBudgetExponent s 1 := by
    exact pow_nonneg (add_nonneg hc.nonnegative (Nat.cast_nonneg _)) _
  apply hc.full.trans
  unfold recursiveParameter finiteFreezingRecursiveParameter
  linarith only [hi, hpower]

theorem input_le_physicalBudget : source.x ≤ source.physicalBudget := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  exact (allocatedCandidateTerminalFullInput_bounds (s + 1) m source.Cprimitive
    source.x_nonneg h.2.1 h.1).2.2.1

theorem input_le_recursiveParameter : source.x ≤ source.recursiveParameter :=
  source.input_le_physicalBudget.trans source.physicalBudget_le_recursiveParameter

theorem recursiveParameter_polynomial : source.recursiveParameter ≤
    (candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) source.physicalBudget :=
  (candidateSourceBackendPolynomial_bounds s source.physicalBudget_nonneg).recursive

theorem affine_floor :
    certifiedAffineLongSideBound
      (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) ≤
      source.separation := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  have hcenter := (allocatedCandidateTerminalFullInput_bounds (s + 1) m source.Cprimitive
    source.x_nonneg h.2.1 h.1).2.2.2.2.2.2.1
  exact candidatePhysicalOrdinaryBudget_separation s source.physicalBudget_nonneg h.1 hcenter

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

theorem physicalBudget_bounds :
    0 ≤ source.physicalBudget ∧
      (source.x + source.Cprimitive) ^ source.Cprimitive ≤ source.physicalBudget ∧
      source.x ≤ source.physicalBudget ∧
      nativePhysicalTerminalWorkBudget (s + 1) source.scheduleExponent source.x ≤
        source.physicalBudget ∧
      ((s + 1 : ℕ) : ℝ) ≤ source.physicalBudget ∧
      (m : ℝ) ≤ source.physicalBudget ∧
      certifiedAffineCenterBudget
        (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) ≤
        source.physicalBudget ∧
      nativePhysicalTerminalWorkBudget (s + 1) source.scheduleExponent source.x +
        (s + 1 : ℕ) * m * certifiedAffineCenterBudget
          (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) ≤
        source.physicalBudget := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  exact allocatedCandidateTerminalFullInput_bounds (s + 1) m source.Cprimitive
    source.x_nonneg h.2.1 h.1

theorem physicalBudget_ge_primitive :
    (source.x + source.Cprimitive) ^ source.Cprimitive ≤ source.physicalBudget :=
  source.physicalBudget_bounds.2.1

theorem affineCenter_le_physicalBudget :
    certifiedAffineCenterBudget
      (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) ≤
      source.physicalBudget :=
  source.physicalBudget_bounds.2.2.2.2.2.2.1

theorem affineBudget_le_physicalBudget :
    nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x ≤
      source.physicalBudget := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  exact (certifiedAffineCenterBudget_primitive_bounds h.1).1.trans
    source.affineCenter_le_physicalBudget

theorem affineMassLog_le_ordinaryBudget :
    (2 * certifiedAffineCenterBudget
      (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) + 3) ^ 3 +
      source.physicalBudget ≤ source.ordinaryBudget := by
  have hAffine := (nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg).1
  have hcenter0 := hAffine.trans (certifiedAffineCenterBudget_primitive_bounds hAffine).1
  have hcenter := source.affineCenter_le_physicalBudget
  have hpow :
      (2 * certifiedAffineCenterBudget
        (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) + 3) ^ 3 ≤
        (2 * source.physicalBudget + 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hcenter]) 3
  have hsum :
      (2 * certifiedAffineCenterBudget
        (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) + 3) ^ 3 +
        source.physicalBudget ≤ (2 * source.physicalBudget + 3) ^ 3 + source.physicalBudget := by
    linarith only [hpow]
  exact hsum.trans (candidatePhysicalOrdinaryBudget_bounds source.physicalBudget_nonneg).2.2.1

theorem factorMass_lower {familyP factorLoss massH : ℝ}
    (hmass : Real.exp (-familyP) ≤ massH)
    (hloss : factorLoss + familyP ≤ source.gainLog) :
    Real.exp (-source.physicalBudget) ≤ Real.exp (-factorLoss) * massH := by
  have hbudget : factorLoss + familyP ≤ source.physicalBudget :=
    (hloss.trans source.gain_range.2).trans source.input_le_physicalBudget
  calc
    _ ≤ Real.exp (-factorLoss) * Real.exp (-familyP) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hbudget]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)

theorem affineMass_lower {mass : ℝ}
    (hmass : Real.exp (-source.physicalBudget) ≤ mass) :
    Real.exp (-source.ordinaryBudget) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget
        (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) + 3) ^ 3)) *
        mass := by
  have h := nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive
    source.scheduleExponent source.x_nonneg
  exact candidatePhysicalOrdinaryBudget_mass source.physicalBudget_nonneg h.1
    source.affineCenter_le_physicalBudget hmass

theorem affineFactorMass_lower {familyP factorLoss massH : ℝ}
    (hmass : Real.exp (-familyP) ≤ massH)
    (hloss : factorLoss + familyP ≤ source.gainLog) :
    Real.exp (-source.ordinaryBudget) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget
        (nativePhysicalTerminalAffineBudget (s + 1) source.scheduleExponent source.x) + 3) ^ 3)) *
        (Real.exp (-factorLoss) * massH) :=
  source.affineMass_lower (source.factorMass_lower hmass hloss)

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
