import OAI.Combinatorics.Progressions.Estimates.AllocatedInactiveNaturalShort

namespace OAI

section

namespace Erdos3.VectorPolynomial

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
local notation "cost" => (2 : ℝ) ^ (degree + 1)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

theorem exists_allocated_inactive_natural_spectrum
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hgamma : gamma ≤ 1)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P ε : ℝ)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
    let ζ := uniformBlockRetainedBias j.val rows.card (degree * rows.card) P
      ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ε
    ∃ F : Finset (rows → Fin (torus * scale)),
      (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card (degree * rows.card) P
        ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * (degree * rows.card)) ∧
      (∑ k, ‖∏ a, weightedCubeGridCoefficient (source a) (torus * scale) rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ∧
      (∀ k ∈ F, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤
        uniformCharacterDenominatorBound j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ζ ∧
        ∃ (a : rows → ℤ) (ξ : rows → ℝ),
          (∀ t, |ξ t| ≤ 2 * majorArcCoverConstant j.val rows.card P ((torus : ℝ) * cost) /
            ζ ^ majorArcCoverExponent j.val rows.card) ∧
          ∀ t, ((k t).val : ℝ) / (torus * scale) = (a t : ℝ) / d + ξ t / scale) ∧
      ∀ shift z : rows → ℤ,
        (∀ t, |(z t : ℝ) - shift t| ≤ blockJetScaleBound (Fintype.card α) degree
          (Fintype.card (B ⟨j, Sum.inr i⟩)) 1 * scale) →
        ‖(((scale : ℝ) ^ rows.card *
            (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
          weightedCubeGridApproximation source scale (torus * scale) rows shift z F‖ ≤ ε := by
  let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
  have hs (a : B ⟨j, Sum.inr i⟩) (v : Fin degree) : ScalarCubePrimitiveBudget (source a v) A P :=
    (allocatedLocalResidueSources_primitive B U b S j i q hq r hsize a v A).mono hP
  have hP1 : 1 ≤ P :=
    (hs (Classical.choice (inferInstance : Nonempty (B ⟨j, Sum.inr i⟩))) ⟨0, Nat.zero_lt_succ _⟩).one_le
  obtain ⟨hu, hl, hp⟩ := allocatedInactiveResidueSources_natural_scale B U b S j i q hq r hsize hR hgamma hsmall hlarge
  obtain ⟨F, hcard, hcap, hchar, herr⟩ := weightedCube_integer_density_approximation (K := scale)
    source A hA hP1 zero_le_one (by positivity) (by positivity) hε hε1 hs
    (fun a => by simpa only [one_mul] using hu a) hl degree hp rows hrows hB
  refine ⟨F, hcard, hcap, hchar, ?_⟩
  intro shift z hz
  have h := herr shift z hz
  rw [finiteImageMass_eq_toPMF,
    allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows shift] at h
  exact h

end Erdos3.VectorPolynomial

end

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
local notation "cost" => (2 : ℝ) ^ (degree + 1)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 2
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem exists_forecastInactive_fixed_spectrum
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hgamma : gamma ≤ 1) (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P ε : ℝ)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
    let ζ := uniformBlockRetainedBias j.val rows.card (degree * rows.card) P
      ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ε
    ∃ F : Finset (rows → Fin (torus * scale)),
      (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card (degree * rows.card) P
        ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * (degree * rows.card)) ∧
      (∑ k, ‖∏ a, weightedCubeGridCoefficient (source a) (torus * scale) rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ∧
      (∀ k ∈ F, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤
        uniformCharacterDenominatorBound j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ζ ∧
        ∃ (a : rows → ℤ) (ξ : rows → ℝ),
          (∀ t, |ξ t| ≤ 2 * majorArcCoverConstant j.val rows.card P ((torus : ℝ) * cost) /
            ζ ^ majorArcCoverExponent j.val rows.card) ∧
          ∀ t, ((k t).val : ℝ) / (torus * scale) = (a t : ℝ) / d + ξ t / scale) ∧
      ∀ shift z : rows → ℤ,
        ‖(((scale : ℝ) ^ rows.card *
            (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
          weightedCubePlateauApproximation source scale radius rows shift z F‖ ≤ ε := by
  let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
  have hs (a : B ⟨j, Sum.inr i⟩) (v : Fin degree) : ScalarCubePrimitiveBudget (source a v) A P :=
    (allocatedLocalResidueSources_primitive B U b S j i q hq r hsize a v A).mono hP
  have hP1 : 1 ≤ P :=
    (hs (Classical.choice (inferInstance : Nonempty (B ⟨j, Sum.inr i⟩))) ⟨0, Nat.zero_lt_succ _⟩).one_le
  obtain ⟨hu, hl, hp⟩ := allocatedInactiveResidueSources_natural_scale B U b S j i q hq r hsize hR hgamma hsmall hlarge
  have hu2 a : (∏ v, ((source a v).length : ℝ)) ≤ 2 * scale :=
    (hu a).trans (by linarith only [show (0 : ℝ) ≤ scale from Nat.cast_nonneg _])
  obtain ⟨F, hcard, hcap, hchar, herr⟩ := weightedCube_integer_density_approximation (K := scale)
    source A hA hP1 (show (0 : ℝ) ≤ 2 by norm_num) (by positivity) (by positivity) hε hε1 hs
    hu2 hl degree hp rows hrows hB
  refine ⟨F, hcard, hcap, hchar, ?_⟩
  have hpoint (shift z : rows → ℤ) :
      ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
        weightedCubePlateauApproximation source scale radius rows shift z F‖ ≤ ε := by
    apply weightedCubePlateauApproximation_error source zero_le_one (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
      (fun a => by simpa only [one_mul] using hu a) rows hrows shift z _
      (allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows shift)
      F hε.le
    intro hz
    have hbuffer := blockJetScaleBound_buffer_le_double (Fintype.card α) degree
      (Fintype.card (B ⟨j, Sum.inr i⟩)) Fintype.card_pos
    have h := herr shift z (fun t => (hz t).trans
      (mul_le_mul_of_nonneg_right hbuffer (Nat.cast_nonneg scale)))
    rw [finiteImageMass_eq_toPMF,
      allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows shift] at h
    exact h
  exact hpoint

end Erdos3.VectorPolynomial

end

end OAI
