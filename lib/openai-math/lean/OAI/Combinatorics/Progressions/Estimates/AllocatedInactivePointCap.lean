import OAI.Combinatorics.Progressions.Fourier.AllocatedInactiveGridSpectrum
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 2
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
noncomputable def allocatedInactivePlateauApproximation
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) : ℂ :=
  ∫ c, weightedCubePlateauApproximation source height radius rows
    (fun t => booleanCoefficient (fun _ : Finset α => c) t) z F ∂(constantLaw).toMeasure

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedInactivePlateauApproximation_norm_le
    {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (z : rows → ℤ) (F : Finset (rows → Fin M)) {C : ℝ}
    (hcap : (∑ k, ‖∏ a, weightedCubeGridCoefficient (source a) M rows k‖) ≤ C) :
    ‖allocatedInactivePlateauApproximation B U b S j i q hq r hsize hR hσ M rows z F‖ ≤ C := by
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (b j) i)
  unfold allocatedInactivePlateauApproximation
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (ae_of_all (constantLaw).toMeasure (fun c =>
      weightedCubePlateauApproximation_norm_le source radius rows _ z F hscale hcap))

theorem exists_allocated_inactive_plateau_spectrum
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P ε : ℝ)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    letI : NeZero height := ⟨(basisAxisScale_pos (b j) i).ne'⟩
    let ζ := uniformBlockRetainedBias j.val rows.card (degree * rows.card) P
      ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ε
    ∃ F : Finset (rows → Fin (torus * height)),
      (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card (degree * rows.card) P
        ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * (degree * rows.card)) ∧
      (∑ k, ‖∏ a, weightedCubeGridCoefficient (source a) (torus * height) rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ∧
      (∀ k ∈ F, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤
        uniformCharacterDenominatorBound j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ζ ∧
        ∃ (a : rows → ℤ) (ξ : rows → ℝ),
          (∀ t, |ξ t| ≤ 2 * majorArcCoverConstant j.val rows.card P ((torus : ℝ) * cost) /
            ζ ^ majorArcCoverExponent j.val rows.card) ∧
          ∀ t, ((k t).val : ℝ) / (torus * height) = (a t : ℝ) / d + ξ t / height) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ),
        ‖(((height : ℝ) ^ rows.card *
            (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ) -
          allocatedInactivePlateauApproximation B U b S j i q hq r hsize hR hσ
            (torus * height) rows z F‖ ≤ ε := by
  let : NeZero height := ⟨(basisAxisScale_pos (b j) i).ne'⟩
  have hs (a : B ⟨j, Sum.inr i⟩) (v : Fin degree) : ScalarCubePrimitiveBudget (source a v) A P :=
    (allocatedLocalResidueSources_primitive B U b S j i q hq r hsize a v A).mono hP
  have hP1 : 1 ≤ P :=
    (hs (Classical.choice (inferInstance : Nonempty (B ⟨j, Sum.inr i⟩))) ⟨0, Nat.zero_lt_succ _⟩).one_le
  obtain ⟨hu, hl, hp⟩ := allocatedInactiveResidueSources_scale B U b S j i q hq r hsize hsmall hlarge
  have hu2 a : (∏ v, ((source a v).length : ℝ)) ≤ 2 * height :=
    (hu a).trans (by linarith only [show (0 : ℝ) ≤ height from Nat.cast_nonneg _])
  obtain ⟨F, hcard, hcap, hchar, herr⟩ := weightedCube_integer_density_approximation (K := height)
    source A hA hP1 (show (0 : ℝ) ≤ 2 by norm_num) (by positivity) (by positivity) hε hε1 hs
    hu2 hl degree hp rows hrows hB
  refine ⟨F, hcard, hcap, hchar, ?_⟩
  have hpoint (shift z : rows → ℤ) :
      ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
        weightedCubePlateauApproximation source height radius rows shift z F‖ ≤ ε := by
    apply weightedCubePlateauApproximation_error source zero_le_one (basisAxisScale_pos (b j) i)
      (fun a => by simpa only [one_mul] using hu a) rows hrows shift z _
      (allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows shift)
      F hε.le
    intro hz
    have hbuffer := blockJetScaleBound_buffer_le_double (Fintype.card α) degree
      (Fintype.card (B ⟨j, Sum.inr i⟩)) Fintype.card_pos
    have h := herr shift z (fun t => (hz t).trans
      (mul_le_mul_of_nonneg_right hbuffer (Nat.cast_nonneg height)))
    rw [finiteImageMass_eq_toPMF,
      allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows shift] at h
    exact h
  intro x z
  unfold allocatedSupportedPhysicalGridPMF allocatedInactivePlateauApproximation
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_point_approximation_error (constantLaw) _ z _ (pow_nonneg (Nat.cast_nonneg height) _)
  intro c
  exact hpoint _ z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 2
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

variable (rows : Finset (Finset α)) (P ε : ℝ)

local notation "bias" => uniformBlockRetainedBias (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) ε
local notation "sizeBound" => uniformSpectrumSizeConstant (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) /
  ε ^ max (majorArcSpectrumExponent (Fin.val j) (Finset.card rows)) (majorArcLengthExponent (Fin.val j) * (degree * Finset.card rows))
local notation "cap" => uniformSpectrumAbsoluteCap (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows)
local notation "periodBound" => uniformCharacterDenominatorBound (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) bias
local notation "frequencyBound" => 2 * majorArcCoverConstant (Fin.val j) (Finset.card rows) P ((torus : ℝ) * cost) /
  bias ^ majorArcCoverExponent (Fin.val j) (Finset.card rows)
local notation "freq" => Real.toNNReal frequencyBound
local notation "supportRadius" => (Finset.card rows : ℝ) * (radius + R j / 4)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "smallHeight" => (max (2 * denom)
  (integerAxisShortBound degree ((Fintype.card α + 1) * q) gamma) : ℕ)
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "shortRadius" => (Finset.card rows : ℝ) * ((Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
local notation "commonRadius" => max supportRadius shortRadius + 1 / 4

include hq in
theorem allocatedInactiveGrid_normalized_norm_le
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hsmall : height ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      max (cap + 1) ((smallHeight : ℝ) ^ rows.card) := by
  let : NeZero height := ⟨(basisAxisScale_pos (b j) i).ne'⟩
  rcases allocatedGridSide_normalizable_or_bounded B U b S q j i hq hsize with hl | hs
  · obtain ⟨F, _, hcap, _, he⟩ := exists_allocated_inactive_plateau_spectrum B U b S j i q hq r hl.2
      hR hσ hsmall hl.1 hcell hgrid A hA P 1 hP zero_lt_one le_rfl rows hrows hB
    have hb := allocatedInactivePlateauApproximation_norm_le B U b S j i q hq r hl.2
      hR hσ (M := torus * height) rfl rows z F hcap
    have ht := norm_sub_le_norm_sub_add_norm_sub
      ((((height : ℝ) ^ rows.card *
        (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ))
      (allocatedInactivePlateauApproximation B U b S j i q hq r hl.2 hR hσ (torus * height) rows z F) 0
    simp only [sub_zero] at ht
    exact ((ht.trans (add_le_add (he x z) hb)).trans_eq (add_comm 1 cap)).trans (le_max_left _ _)
  · have hp : (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg)]
    exact ((mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg _) _) hp).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs) _)).trans (le_max_right _ _)

end Erdos3.VectorPolynomial

end

end OAI
