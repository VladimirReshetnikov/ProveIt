import OAI.Combinatorics.Progressions.Estimates.AllocatedPlateauSiteApproximation
import OAI.Combinatorics.Progressions.Estimates.SitePlateauCutoff

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem real_coordinate_support_add {J : Type*} (z center : J → ℤ) {H C K : ℝ}
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K)
    (hc : ∀ j, |(center j : ℝ)| ≤ C * K) :
    ∀ j, |(z j : ℝ)| ≤ (H + C) * K := by
  intro j
  calc
    _ = |((z j : ℝ) - center j) + center j| := by congr 1; ring
    _ ≤ |(z j : ℝ) - center j| + |(center j : ℝ)| := abs_add_le _ _
    _ ≤ H * K + C * K := add_le_add (hz j) (hc j)
    _ = _ := by ring

theorem pmf_bind_zero_of_support {X Y : Type*} (p : PMF X) (q : X → PMF Y) (z : Y)
    (hz : ∀ x ∈ p.support, q x z = 0) : p.bind q z = 0 := by
  rw [PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : p x = 0
  · rw [hx, zero_mul]
  · rw [hz x hx, mul_zero]

theorem pmf_integral_zero_of_support {X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) (f : X → ℂ) (hf : ∀ x ∈ p.support, f x = 0) :
    (∫ x, f x ∂p.toMeasure) = 0 := by
  calc
    _ = ∫ x in p.support, f x ∂p.toMeasure := by rw [p.restrict_toMeasure_support]
    _ = 0 := integral_eq_zero_of_ae
      ((ae_restrict_mem p.support_countable.measurableSet).mono (fun x hx => hf x hx))

theorem weightedModeratePlateauApproximation_zero_off_window
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n K M : ℕ} [NeZero M]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (hK : 0 < K) (H C : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M))
    (hshift : ∀ t, |(shift t : ℝ)| ≤ C * K)
    (hz : ¬∀ t, |(z t : ℝ)| ≤ (H + 1 / 4 + C) * K) :
    weightedModeratePlateauApproximation c s offset K H rows shift z F = 0 := by
  have hχ : normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) = 0 := by
    by_contra hχ
    exact hz (real_coordinate_support_add z shift
      (normalizedSupportPlateau_grid_support hK shift z hχ) hshift)
  simp only [weightedModeratePlateauApproximation, hχ, Complex.ofReal_zero, zero_mul]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedNaturalConstantRadius (j : Fin m) (i : Fin (n j)) : ℝ :=
  2 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)

noncomputable def allocatedNaturalSupportRadius (α : Type*) [Fintype α]
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4 +
    1 / 4 + allocatedNaturalConstantRadius (G := G) B j i

omit [Fintype G] [∀ j, Fintype (I j)] in
theorem allocatedNaturalSupportRadius_nonneg (α : Type*) [Fintype α]
    (j : Fin m) (i : Fin (n j)) : 0 ≤ allocatedNaturalSupportRadius (G := G) B α j i := by
  have h := blockJetScaleBound_nonneg (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) (by norm_num : (0 : ℝ) ≤ 4)
  unfold allocatedNaturalSupportRadius allocatedNaturalConstantRadius
  positivity

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "constantRadius" => allocatedNaturalConstantRadius (G := G) B j i

include hactive in
theorem allocatedNaturalConstantLaw_bound (c : ℤ) (hc : c ∈ (constantLaw).support) :
    |(c : ℝ)| ≤ constantRadius * scale := by
  change c ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i (constantCoefficientSlot _ _)).support at hc
  rw [allocatedLayerIntegerPMFs_constant B U basis hR hσ S j i] at hc
  have hk : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hb := constantIntegerPMF_support (basisAxisScale (basis j) i) (R j / 4) hk
    (div_pos (hR j) (by norm_num)) hc
  have hdiv : |(c : ℝ) / basisAxisScale (basis j) i| ≤ R j / 4 := by linarith [hR j]
  rw [abs_div, abs_of_pos hk] at hdiv
  have he : R j / 4 = constantRadius * gamma := by
    unfold allocatedNaturalConstantRadius principalProfileSize
    field_simp
    ring
  calc
    |(c : ℝ)| ≤ (R j / 4) * basisAxisScale (basis j) i := (div_le_iff₀ hk).mp hdiv
    _ = constantRadius * (gamma * basisAxisScale (basis j) i) := by rw [he]; ring
    _ ≤ constantRadius * scale := mul_le_mul_of_nonneg_left
      (allocatedPrincipalGridScale_bounds B U basis hR S j i hactive).1
      (by unfold allocatedNaturalConstantRadius; positivity)

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
include hactive in
theorem allocatedNaturalConstantShift_bound (c : ℤ) (hc : c ∈ (constantLaw).support)
    (t : Finset α) :
    |((booleanCoefficient (fun _ : Finset α => c) t : ℤ) : ℝ)| ≤ constantRadius * scale := by
  rw [booleanCoefficient_const]
  split_ifs
  · exact allocatedNaturalConstantLaw_bound B U basis hR hσ S j i hactive c hc
  · simp only [Int.cast_zero, abs_zero]
    unfold allocatedNaturalConstantRadius
    positivity

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize
local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "radius" => allocatedNaturalSupportRadius (G := G) B α j i
local notation "principalRadius" => blockJetScaleBound (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

include hactive hq hsize in
theorem allocatedNaturalPhysicalPoint_zero_off_window
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ)
    (hz : ¬∀ t, |(z t : ℝ)| ≤ radius * scale) :
    allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x z = 0 := by
  unfold allocatedSupportedPhysicalGridPMF
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U basis hR hσ S q r hcell j i hgrid rows x]
  apply pmf_bind_zero_of_support
  intro c hc
  apply weightedModeratePMF_zero_off_scaled_support (fun _ : B ⟨j, Sum.inr i⟩ => csource)
    sources (fun _ => 0) (by norm_num : (0 : ℝ) ≤ 4)
    (allocatedActiveResidueSources_natural_volume B U basis hR S q r j i hactive hq hsize)
    rows hrows (fun t => booleanCoefficient (fun _ : Finset α => c) t) z
    (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows _)
    (allocatedSupportedResidueJetPMF_source B U basis hR hσ S q r hcell j i hactive hq hsize rows _)
  intro hrelative
  apply hz
  have hglobal := real_coordinate_support_add z (fun t => booleanCoefficient (fun _ : Finset α => c) t)
    hrelative (fun t => allocatedNaturalConstantShift_bound B U basis hR hσ S j i hactive c hc (t : Finset α))
  intro t
  apply (hglobal t).trans
  change (principalRadius + constantRadius) * (scale : ℝ) ≤
    (principalRadius + 1 / 4 + constantRadius) * (scale : ℝ)
  gcongr
  norm_num

theorem allocatedNaturalPlateau_zero_off_window
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ) (F : Finset (rows → Fin M))
    (hz : ¬∀ t, |(z t : ℝ)| ≤ radius * scale) :
    allocatedConstantPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize M rows z F = 0 := by
  unfold allocatedConstantPlateauApproximation
  apply pmf_integral_zero_of_support
  intro c hc
  exact weightedModeratePlateauApproximation_zero_off_window
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) sources (fun _ => 0)
    (allocatedPrincipalGridScale_pos B U basis hR S j i hactive) principalRadius constantRadius
    rows (fun t => booleanCoefficient (fun _ : Finset α => c) t) z F
    (fun t => allocatedNaturalConstantShift_bound B U basis hR hσ S j i hactive c hc (t : Finset α)) hz

theorem allocatedBudgetedPlateau_zero_off_window (P ε : ℝ)
    (M : ℕ) [NeZero M] (rows : Finset (Finset α)) (z : rows → ℤ)
    (hz : ¬∀ t, |(z t : ℝ)| ≤ radius * scale) :
    allocatedBudgetedPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize P ε M rows z = 0 :=
  allocatedNaturalPlateau_zero_off_window B U basis hR hσ S j i hactive q r hq hsize M rows z _ hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def allocatedNaturalSiteRadius (j : Fin m) (i : Fin (n j))
    (rows : Finset (Finset α)) : ℝ :=
  rows.card * allocatedNaturalSupportRadius (G := G) B α j i

omit [Fintype G] [∀ j, Fintype (I j)] [DecidableEq α] in
theorem allocatedNaturalSiteRadius_nonneg (j : Fin m) (i : Fin (n j))
    (rows : Finset (Finset α)) : 0 ≤ allocatedNaturalSiteRadius (G := G) B j i rows :=
  mul_nonneg (Nat.cast_nonneg _) (allocatedNaturalSupportRadius_nonneg B α j i)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i

include hactive hq hsize in
theorem allocatedNaturalPhysicalSites_bound
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ)
    (hy : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (hmass : allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
      (fun t => booleanCoefficient y t) ≠ 0) :
    ∀ s, |(y s : ℝ) / scale| ≤ allocatedNaturalSiteRadius (G := G) B j i rows := by
  have hcoeff : ∀ t : rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤
      allocatedNaturalSupportRadius (G := G) B α j i * scale := by
    by_contra hn
    exact hmass (allocatedNaturalPhysicalPoint_zero_off_window B U basis hR hσ S j i hactive q r hq hsize
      hcell hgrid rows hrows x (fun t => booleanCoefficient y t) hn)
  intro s
  exact integer_boolean_sites_bound y rows hy
    (allocatedNaturalSupportRadius_nonneg B α j i)
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos B U basis hR S j i hactive))
    (fun t ht => hcoeff ⟨t, ht⟩) s

include hactive hq hsize in
theorem allocatedNaturalPhysicalSites_zero_off_box
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ)
    (hy : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (hlarge : ∃ s, allocatedNaturalSiteRadius (G := G) B j i rows < |(y s : ℝ) / scale|) :
    allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
      (fun t => booleanCoefficient y t) = 0 := by
  by_contra hmass
  obtain ⟨s, hs⟩ := hlarge
  exact (not_lt_of_ge (allocatedNaturalPhysicalSites_bound B U basis hR hσ S j i hactive q r hq hsize
    hcell hgrid rows hrows x y hy hmass s)) hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable {M : ℕ} [NeZero M] (rows : Finset (Finset α)) (P ε : ℝ)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "bias" => positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
  P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ε
local notation "spectrum" => positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value bias
local notation "cap" => allocatedGridPointCap B P (Sigma.mk j i) rows
local notation "freq" => Real.toNNReal (positiveRetainedFrequencyBound j.val rows.card P (torus : ℝ) bias)
local notation "chartRatio" => allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i
local notation "supportRadius" => allocatedNaturalSiteRadius (G := G) B j i rows

include hactive hq hsize in
theorem exists_allocated_supported_site_approximation
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hgamma : gamma ≤ S.value) (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : M = torus * scale) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : supportRadius + 1 / 4 ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    ∃ D : (rows → Fin M) → ℕ, (∀ k, 0 < D k) ∧
      (∀ k ∈ spectrum, (D k : ℝ) ≤ positiveRetainedDenominatorBound j.val rows.card
        ((layerTailDegree m + 2) * rows.card) P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) bias) ∧
      ∃ N : spectrum → ℕ, (∀ k, (N k : ℝ) ≤ Real.exp (4 * Q + 8)) ∧
        (Fintype.card (PlateauSiteIndex α spectrum N) : ℝ) ≤
          (Finset.card spectrum) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)) ∧
        ∃ (β : PlateauSiteIndex α spectrum N → ℂ)
          (f : (k : PlateauSiteIndex α spectrum N) → Finset α → ZMod (D k.1) → ℝ → ℂ),
          (∑ k, ‖β k‖) ≤ cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q) ∧
          (∀ k u v z, ‖f k u v z‖ ≤ 1) ∧
          (∀ k u v, LipschitzWith (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (f k u v)) ∧
          (∀ k u v z, supportRadius + 1 / 4 ≤ |z| → f k u v z = 0) ∧
          ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
            (∀ t ∉ rows, booleanCoefficient y t = 0) →
            (‖(((scale : ℝ) ^ rows.card *
                (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
                  (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
              ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale)‖ ≤ ε + δ) ∧
            ‖(basisAxisScale (basis j) i : ℂ) ^ rows.card *
                ((allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
                  (fun t => booleanCoefficient y t)).toReal : ℂ) -
              ∑ k, ((chartRatio : ℂ) ^ rows.card * β k) * ∏ u,
                f k u (y u : ZMod (D k.1)) (chartRatio * ((y u : ℝ) / basisAxisScale (basis j) i))‖ ≤
              chartRatio ^ rows.card * (ε + δ) := by
  have hr : 0 ≤ supportRadius := allocatedNaturalSiteRadius_nonneg B j i rows
  obtain ⟨D, hD, hDb, N, hN, hcard, β, f, hβ, hf, hLf, he⟩ :=
    exists_allocated_physical_site_approximation B U basis hR hσ S q r j i hactive hq hsize rows P ε
      hcell hgrid hgamma L hL hcP hsP hM hrows hB hε hε1
      (H := supportRadius + 1 / 4) (by positivity) hδ hQ hHQ hδQ hLQ
  let g (k : PlateauSiteIndex α spectrum N) (u : Finset α) (v : ZMod (D k.1)) (z : ℝ) : ℂ :=
    scalarSupportPlateau supportRadius z * f k u v z
  refine ⟨D, hD, hDb, N, hN, hcard, β, g, hβ, ?_, ?_, ?_, ?_⟩
  · intro k u v z
    dsimp only [g]
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz supportRadius (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    dsimp only [g]
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro x y hy
    have hkeep :
        (((scale : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) ≠ 0 →
        ∀ u, scalarSupportPlateau supportRadius ((y u : ℝ) / scale) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hr
        (allocatedNaturalPhysicalSites_bound B U basis hR hσ S j i hactive q r hq hsize
          hcell hgrid rows hrows x y hy hmass u)
    have herr := finite_site_cutoff_error _ β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale))
      (fun u => scalarSupportPlateau supportRadius ((y u : ℝ) / scale))
      (show 0 ≤ ε + δ by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
      (fun hcut => (he x y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le)).1)
    refine ⟨herr, ?_⟩
    have ht := grid_site_normalization_error
      (K := (basisAxisScale (basis j) i : ℝ)) (N := (scale : ℝ))
      (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
      (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)) rows.card
      ((allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
        (fun t => booleanCoefficient y t)).toReal : ℂ)
      β (fun k u z => g k u (y u : ZMod (D k.1)) z) (fun u => (y u : ℝ))
      (by simpa only [g, Complex.ofReal_mul, Complex.ofReal_pow] using herr)
    simpa only [Complex.ofReal_natCast, allocatedPrincipalChartRatio] using ht

end Erdos3.VectorPolynomial

end

end OAI
