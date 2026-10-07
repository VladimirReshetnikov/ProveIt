import OAI.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem preparedFiniteForwardFixedCenterThreshold_le_seed_half
    (A : ℕ) (constants : ℕ → ℕ) (stage : ℕ)
    {x gainLog stageLog : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : 0 ≤ gainLog) (hs : 0 ≤ stageLog) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A constants stage x gainLog stageLog +
      4 * preparedFiniteForwardWork A constants stage x + 8)) ≤ Real.exp (-x) / 2 := by
  have hwork : x + 1 ≤ preparedFiniteForwardWork A constants stage x := by
    simpa only [Nat.cast_one, pow_one] using
      preparedFiniteForward_shiftedPower_le_work A 1 constants stage hA (by omega) hx
  have hw0 := preparedFiniteForwardWork_nonneg A constants stage hx
  have hprefix := (preparedFiniteForward_prefix_bounds A constants stage hx).2.1
  have hfloor : x + 1 ≤
      2 * preparedFiniteForwardModelPrecision A constants stage x gainLog stageLog +
        4 * preparedFiniteForwardWork A constants stage x + 8 := by
    unfold preparedFiniteForwardModelPrecision
    linarith only [hwork, hw0, hprefix, hg, hs]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(x + 1)) ≤ Real.exp (-x) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(x + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht := Real.exp_le_exp.mpr (neg_le_neg hfloor)
  linarith only [ht, hhalf]

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile

noncomputable def raise_gain {degree : ℕ} (P : sampler.InnerSourceProfile degree)
    (gain : ℝ) (hgain : P.gainLog ≤ gain) (hgainx : gain ≤ P.x)
    (hloss : ∀ r < degree, P.detectionLoss r ≤ Real.exp (-gain) / 2) :
    sampler.InnerSourceProfile degree := by
  refine { P with
    gainLog := gain
    gain_range := ⟨P.gain_range.1.trans hgain, hgainx⟩
    source_bound := ?_
    loss_bound := hloss
  }
  intro r hr
  apply (P.source_bound r hr).trans
  have hsource0 := (preparedFiniteForward_model_precision_bounds
    P.scheduleExponent AllocatedExternalCandidateSampler.degreeSourceCountConstants r
    P.x_nonneg P.gain_range P.stage_range).2.1
  have hwork0 := preparedFiniteForwardWork_nonneg P.scheduleExponent
    AllocatedExternalCandidateSampler.degreeSourceCountConstants r P.x_nonneg
  apply pow_le_pow_left₀ (add_nonneg (add_nonneg hsource0 hwork0) (Nat.cast_nonneg _))
  unfold preparedFiniteForwardSourcePrecision preparedFiniteForwardModelPrecision
  linarith only [hgain]

noncomputable def with_gain_detection {degree : ℕ} (P : sampler.InnerSourceProfile degree)
    (gain : ℝ) (hgain : P.gainLog ≤ gain) (hgainx : gain ≤ P.x)
    (loss : ℕ → ℝ) (hzero : ∀ r < degree, 0 ≤ loss r)
    (hloss : ∀ r < degree, loss r ≤ Real.exp (-gain) / 2)
    (hdetect : ∀ r < degree, sampler.NativeDetection r
      (allocatedCandidateStageSlice degree m P.Cprimitive
        (preparedFiniteForwardParameter P.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants r P.x))
      (P.pTest r) (P.sourceNative r) (loss r)) :
    sampler.InnerSourceProfile degree := by
  have hweaken : Real.exp (-gain) / 2 ≤ Real.exp (-P.gainLog) / 2 :=
    div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hgain)) (by norm_num)
  let Q : sampler.InnerSourceProfile degree := { P with
    detectionLoss := loss
    loss_nonneg := hzero
    loss_bound := fun r hr => (hloss r hr).trans hweaken
    detection := hdetect
  }
  exact Q.raise_gain gain hgain hgainx hloss

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
