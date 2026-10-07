import OAI.Combinatorics.Progressions.Estimates.AllocatedInactiveJointSite

namespace OAI

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
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (2 : ℝ) ^ (degree + 1)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "constantRadius" => 2 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
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
local notation "supportRadius" => (Finset.card rows : ℝ) * (radius + constantRadius)

include hq hsize in
theorem exists_forecastInactive_fixed_site_expansion
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hgamma : gamma ≤ 1) (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ)
    (hc : (constantLaw) c ≠ 0)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : supportRadius + 1 / 4 ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (sizeBound * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        periodBound
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (supportRadius + 1 / 4) ∧
      ∀ (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε + δ := by
  let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
  obtain ⟨F, hcard, hcap, hchar, hpoint⟩ := exists_forecastInactive_fixed_spectrum
    B U b S j i q hq r hsize hR hσ hgamma hsmall hlarge hcell A hA P ε hP hε hε1 rows hrows hB
  have hmodes : ∀ k : rows → Fin (torus * scale), ∃ (d : ℕ) (a : rows → ℤ) (ω : rows → ℝ),
      0 < d ∧ (k ∈ F → (d : ℝ) ≤ periodBound ∧ (∀ t, |ω t| ≤ frequencyBound) ∧
        ∀ t, ((k t).val : ℝ) / (torus * scale) = (a t : ℝ) / d + ω t / scale) := by
    intro k
    by_cases hk : k ∈ F
    · obtain ⟨d, hd, hdb, a, ω, hω, he⟩ := hchar k hk
      exact ⟨d, a, ω, hd, fun _ => ⟨hdb, hω, he⟩⟩
    · exact ⟨1, fun _ => 0, fun _ => 0, zero_lt_one, fun h => False.elim (hk h)⟩
  choose D a ω hD hmodes using hmodes
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  have hscale : ((scale : ℝ) / (torus * scale)) ^ rows.card ≤ 1 :=
    grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  have hsupport : 0 ≤ supportRadius := mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (blockJetScaleBound_nonneg _ _ _ zero_le_one) (by positivity))
  obtain ⟨N, _, hNcard, β, f, hβ, hf, hLf, he⟩ := exists_weightedCube_plateau_site_approximation source
    (PMF.pure c) (allocatedPrincipalGridScale_pos_of_radius B U b hR j i) radius rows F D a ω
    (fun k hk => by simpa only [Nat.cast_mul] using (hmodes k hk).2.2)
    (fun c t => booleanCoefficient (fun _ : Finset α => c) t)
    (by simpa only [Nat.cast_mul] using hscale) hcap freq
    (fun k hk t => ((hmodes k hk).2.1 t).trans (Real.le_coe_toNNReal _))
    (show 0 < supportRadius + 1 / 4 by linarith only [hsupport]) hδ hQ hHQ hδQ hLQ
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := fun k u v z => scalarSupportPlateau supportRadius z * f k u v z }
  refine ⟨e, ⟨?_, ?_, ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hNcard.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _))
  · exact fun k => hD k.1
  · exact fun k => (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau supportRadius z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz supportRadius (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau supportRadius z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro y hy
    let target : ℂ := (((scale : ℝ) ^ rows.card *
      (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
        (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
      ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau supportRadius ((y u : ℝ) / scale) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      have hmixed : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x₀
          (fun t => booleanCoefficient y t) ≠ 0 := by
        unfold allocatedSupportedPhysicalGridPMF
        rw [allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x₀]
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨c, hc, hmass⟩
      exact scalarSupportPlateau_one hsupport
        (allocatedInactiveNaturalSites_bound B U b S j i q hq r hsize hR hσ
          hgamma hsmall hlarge hcell hgrid rows hrows x₀ y hy hmixed u)
    apply finite_site_cutoff_error target β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale))
      (fun u => scalarSupportPlateau supportRadius ((y u : ℝ) / scale))
      (show 0 ≤ ε + δ by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have hsite := he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have hp := hpoint (fun t => booleanCoefficient (fun _ : Finset α => c) t)
      (fun t => booleanCoefficient y t)
    simp only [PMF.toMeasure_pure, MeasureTheory.integral_dirac] at hsite
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hp hsite)

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
local notation "cost" => (2 : ℝ) ^ (degree + 1)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "constantRadius" => 2 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)
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
local notation "supportRadius" => (Finset.card rows : ℝ) * (radius + constantRadius)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "smallHeight" => (4 * (2 * ((Fintype.card α + 1) * q)) ^ degree : ℕ)
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "shortRadius" => (Finset.card rows : ℝ) * ((Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)))
local notation "commonRadius" => max supportRadius shortRadius + 1 / 4

include hq in
theorem exists_forecastInactive_fixed_site_all_cases
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : height ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ) (hc : (constantLaw) c ≠ 0)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : commonRadius ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortCap : (smallHeight : ℝ) ^ rows.card ≤ Real.exp Q)
    (hshortLip : ((rows.card * (2 * (smallHeight : ℝ≥0) ^ 2) * (smallHeight : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortError : δ⁻¹ ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max (sizeBound * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8))))
        (max periodBound 1)
        (max (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q)))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) commonRadius ∧
      ∀ (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε + δ := by
  rcases allocatedGridSide_natural_normalizable_or_bounded B U b hR S q j i hq hsize hgamma with hl | hs
  · obtain ⟨e, he, herr⟩ := exists_forecastInactive_fixed_site_expansion B U b S j i q hq r hl.2
      hR hσ rows P ε hgamma hsmall hl.1 hcell hgrid c hc A hA hP hε hε1 hrows hB hδ hQ
      ((add_le_add (le_max_left supportRadius shortRadius) (le_refl (1 / 4 : ℝ))).trans hHQ) hδQ hLQ
    exact ⟨e, he.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) le_rfl
      (add_le_add (le_max_left _ _) (le_refl (1 / 4 : ℝ))), herr⟩
  · obtain ⟨e, he, herr⟩ := exists_forecastInactive_fixed_bounded_site_expansion B U b hR hσ S q r hcell j i
      hσ1 hgrid c hc rows hs hδ hQ
      ((add_le_add (le_max_right supportRadius shortRadius) (le_refl (1 / 4 : ℝ))).trans hHQ)
      hshortCap hshortLip hshortError
    refine ⟨e, he.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) le_rfl
      (add_le_add (le_max_right _ _) (le_refl (1 / 4 : ℝ))), ?_⟩
    intro y hy
    exact (herr y hy).trans (le_add_of_nonneg_left hε.le)

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
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

local notation "degree" => Fin.val j + 1
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hq in
theorem exists_forecastInactive_fixed_budgeted_site
    [Nonempty (B ⟨j, Sum.inr i⟩)] {D P p v ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ) (hc : allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none) c ≠ 0)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val (rowSets j).card (degree * (rowSets j).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let O := allocatedInactiveSiteOutputLog m D p v E
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) ∧
      ∀ (y : Finset α → ℤ),
        (∀ t ∉ rowSets j, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ (rowSets j).card *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i (rowSets j)
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ 2 * ε := by
  have hQ := (allocatedInactiveSiteBudgetLog_bounds m hD.nonneg hp hv hE).1
  obtain ⟨hHQ, hεQ, hLQ, hshortCap, hshortLip, herror⟩ :=
    allocatedInactiveSite_construction_bounds B rowSets hD hα hP hp hv hPp hε hε1 hE hεE q hqv ⟨j, i⟩
  obtain ⟨e, he, herr⟩ := exists_forecastInactive_fixed_site_all_cases
    B U b S j i q hq r hR hσ (rowSets j) P ε hsize hgamma hsmall hcell hgrid c hc hσ1 A hA
    hprimitive hε hε1 hrows hB hε hQ hHQ hεQ hLQ hshortCap hshortLip herror
  obtain ⟨hT, hperiod, hC, hL⟩ := allocatedInactiveSite_output_bounds B rowSets hD hα hP hp hv hPp
    hε hε1 hE hεE ⟨j, i⟩
  refine ⟨e, he.mono hT hperiod hC ?_ (allocatedInactiveSiteRadius_exp_bound B rowSets hD ⟨j, i⟩), ?_⟩
  · exact_mod_cast hL
  · intro y hy
    simpa only [two_mul] using herr y hy

end Erdos3.VectorPolynomial

end

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
variable {α : Type} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (2 : ℝ) ^ (degree + 1)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 2
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
variable (rows : Finset (Finset α)) (P ε : ℝ)

local notation "cap" => uniformSpectrumAbsoluteCap (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows)
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "smallHeight" => (4 * (2 * ((Fintype.card α + 1) * q)) ^ degree : ℕ)
include hq in
theorem forecastInactiveFixed_normalized_norm_le
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : height ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rows → ℤ) :
    ‖(((scale : ℝ) ^ rows.card *
      (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ)‖ ≤
      max (cap + 1) ((smallHeight : ℝ) ^ rows.card) := by
  let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
  rcases allocatedGridSide_natural_normalizable_or_bounded B U b hR S q j i hq hsize hgamma with hl | hs
  · obtain ⟨F, _, hcap, _, he⟩ := exists_forecastInactive_fixed_spectrum B U b S j i q hq r hl.2
      hR hσ hgamma hsmall hl.1 hcell A hA P 1 hP zero_lt_one le_rfl rows hrows hB
    let source := allocatedLocalResidueSources B U b S j i q hq r hl.2
    have hscale : ((scale : ℝ) / ((torus * scale : ℕ) : ℝ)) ^ rows.card ≤ 1 := by
      rw [Nat.cast_mul]
      exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _)
        (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
    have hb := weightedCubePlateauApproximation_norm_le (K := scale) source radius rows shift z F hscale hcap
    have ht := norm_sub_le_norm_sub_add_norm_sub
      ((((scale : ℝ) ^ rows.card *
        (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ))
      (weightedCubePlateauApproximation source scale radius rows shift z F) 0
    simp only [sub_zero] at ht
    exact ((ht.trans (add_le_add (he shift z) hb)).trans_eq (add_comm 1 cap)).trans (le_max_left _ _)
  · have hp : (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg)]
    exact ((mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg _) _) hp).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs) _)).trans (le_max_right _ _)

variable (rowSets : Fin m → Finset (Finset α))

include hq in
theorem forecastInactiveFixed_norm_exp_bound
    [Nonempty (B ⟨j, Sum.inr i⟩)] {D P p v : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val (rowSets j).card (degree * (rowSets j).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    (shift z : rowSets j → ℤ) :
    ‖(((scale : ℝ) ^ (rowSets j).card *
      (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i (rowSets j) shift z).toReal : ℝ) : ℂ)‖ ≤
      Real.exp (allocatedInactivePointCapLog m D p v) := by
  have hb := forecastInactiveFixed_normalized_norm_le B U b S j i q hq r hR hσ
    (rowSets j) P hsize hgamma hsmall hcell A hA hprimitive hrows hB shift z
  have hs := allocatedInactiveSpectrum_exp_bounds B rowSets hD hα hP hp hPp
    (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ)) (le_refl (0 : ℝ))
    (by norm_num : (1 : ℝ)⁻¹ ≤ Real.exp 0) ⟨j, i⟩
  have hrow : ((rowSets j).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using hD.rows j
  have hshort := inactiveNaturalShortResources_exp_bounds (Fintype.card α) (j.val + 1) q
    (rowSets j).card hD.nonneg hv hD.cube (hD.layer_degree B j) hrow hqv
  have hC := allocatedInactiveSpectrumLog_nonneg m hD.nonneg hp (le_refl (0 : ℝ))
  have hN := (inactiveShortLogs_nonneg hD.nonneg hv).2.1
  apply hb.trans
  apply max_le
  · exact hs.1.trans (Real.exp_le_exp.mpr (by unfold allocatedInactivePointCapLog; linarith only [hN]))
  · exact hshort.1.trans (Real.exp_le_exp.mpr (by unfold allocatedInactivePointCapLog; linarith only [hC]))

theorem forecastInactive_fixed_zero_axis_norm_le
    (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
    {D P p v : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hsize : q ≤ S.value) (hR1 : R j ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1))
    (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (c z : ℤ) :
    ‖(((allocatedPrincipalGridScale (G := G) B U b (R := R) j i : ℝ) *
      (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i Finset.univ (fun _ => c)
        (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      Real.exp (allocatedInactivePointCapLog m D p v) := by
  have hγ : principalProfileSize (R j)
      (layerIntegerPrincipalSlots (G := G) B j i).card ≤ 1 := by
    unfold principalProfileSize
    apply (div_le_one (by positivity)).mpr
    have hslots : (0 : ℝ) ≤ (layerIntegerPrincipalSlots (G := G) B j i).card := Nat.cast_nonneg _
    linarith only [hR1, hslots]
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) :
      t.card ≤ j.val + 1 := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val
      (Finset.univ : Finset (Finset Empty)).card
      ((j.val + 1) * (Finset.univ : Finset (Finset Empty)).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩) := by simpa using hB
  have hz := forecastInactiveFixed_norm_exp_bound
    B U b S j i q hq r hR hσ (fun _ => (Finset.univ : Finset (Finset Empty))) hD (by simp) hP hp hv hPp hqv
    (by simpa using hsize) hγ hsmall hcell A hA hprimitive hrows hB' (fun _ => c) (fun _ => z)
  simpa only [Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one] using hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem exists_forecastInactive_fixed_zero_axis_site
    (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
    {D P p v ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : R j ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1))
    (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ) (hc : allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none) c ≠ 0)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let scale := allocatedPrincipalGridScale (G := G) B U b (R := R) j i
    let O := allocatedInactiveSiteOutputLog m D p v E
    ∃ e : ScalarSiteExpansion.{0,0} (Finset Empty),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) ∧
      ∀ (z : ℤ),
        ‖(((scale : ℝ) *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i Finset.univ
            (fun _ => c)
            (fun _ => z)).toReal : ℝ) : ℂ) - e.integerEval scale (fun _ => z)‖ ≤ 2 * ε := by
  dsimp only
  have hγ : principalProfileSize (R j)
      (layerIntegerPrincipalSlots (G := G) B j i).card ≤ 1 := by
    unfold principalProfileSize
    apply (div_le_one (by positivity)).mpr
    have hslots : (0 : ℝ) ≤ (layerIntegerPrincipalSlots (G := G) B j i).card := Nat.cast_nonneg _
    linarith only [hR1, hslots]
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) :
      t.card ≤ j.val + 1 := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val
      (Finset.univ : Finset (Finset Empty)).card
      ((j.val + 1) * (Finset.univ : Finset (Finset Empty)).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩) := by simpa using hB
  obtain ⟨e, he, herr⟩ := exists_forecastInactive_fixed_budgeted_site
    B U b S hR hσ (fun _ => (Finset.univ : Finset (Finset Empty)))
    j i q hq r hD (by simp) hP hp hv hPp hqv hε hε1 hE hεE
    (by simpa using hsize) hγ hsmall hcell hgrid c hc hσ1 A hA hprimitive hrows hB'
  refine ⟨e, he, ?_⟩
  intro z
  have hconst (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => z) t = z := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  have hz := herr (fun _ => z) (by
    intro t ht
    exact (ht (Finset.mem_univ t)).elim)
  have hcconst (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => c) t = c := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  simpa only [hconst, hcconst, Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one] using hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

theorem exists_forecastInactive_fixed_product_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (q : ℕ) (hq : 0 < q)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c : A → ℤ)
    (hc : ∀ a, allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c a) ≠ 0)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
      (selected a).1 (selected a).2
    let O := allocatedInactiveJointSiteLog m D p v E
    ∃ e : A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀ (z : A → ℤ),
        ‖(((∏ a, (scale a : ℝ)) *
          (dependentProductPMF (fun a => allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell
            (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c a))
            (fun a _ => z a)).toReal : ℝ) : ℂ) -
          siteFamilyEval e (fun _ => z) (fun _ a => (z a : ℝ) / scale a)‖ ≤ δ := by
  dsimp only
  let cap := Real.exp (allocatedInactivePointCapLog m D p v)
  let ε := uniformProductAccuracy (Fintype.card A) cap δ / 2
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A)
    (Real.exp_nonneg (allocatedInactivePointCapLog m D p v)) hδ
  have hε : 0 < ε := half_pos hτ
  have hε1 : ε ≤ 1 := by dsimp only [ε, cap]; linarith
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => (Finset.univ : Finset (Finset Empty))) hD)
  have hcapLog := allocatedInactivePointCapLog_nonneg m hD.nonneg hp hv
  have hτinv := uniformProductAccuracy_inverse_exp_bound (Fintype.card A)
    (Real.exp_nonneg _) hδ hD.nonneg hcapLog hE hcount (le_refl cap) hδE
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hεinv : ε⁻¹ ≤ Real.exp (allocatedInactiveJointAccuracyLog m D p v E) := by
    dsimp only [ε]
    rw [inv_div, div_eq_mul_inv]
    have hb := (mul_le_mul htwo hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hb.trans_eq (by unfold allocatedInactiveJointAccuracyLog; congr 1; ring)
  have hprecision := (allocatedInactiveJointLogs_nonneg m hD.nonneg hp hv hE).1
  have heach (a : A) := exists_forecastInactive_fixed_zero_axis_site B U b S hR hσ
    (selected a).1 (selected a).2 q hq r hD hP hp hv hPp hqv hε hε1 hprecision
    hεinv hsize (hR1 a) (hsmall a) hcell (hgrid a) (c a) (hc a) (hσ1 a) L hL hprimitive (hB a)
  choose e he herr using heach
  refine ⟨e, he, ?_⟩
  intro z
  let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
    (selected a).1 (selected a).2
  let g (a : A) : ℂ := (((scale a : ℝ) *
    (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell
      (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c a) (fun _ => z a)).toReal : ℝ) : ℂ)
  have hg (a : A) : ‖g a‖ ≤ cap := forecastInactive_fixed_zero_axis_norm_le
    B U b S hR hσ (selected a).1 (selected a).2 q hq r hD hP hp hv hPp hqv
    hsize (hR1 a) (hsmall a) hcell L hL hprimitive (hB a) (c a) (z a)
  have herr' (a : A) :
      ‖g a - (e a).eval (fun _ => z a) (fun _ => (z a : ℝ) / scale a)‖ ≤
      uniformProductAccuracy (Fintype.card A) cap δ := by
    simpa only [ScalarSiteExpansion.integerEval, ε, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      using herr a (z a)
  have hp' := siteFamily_approximation e (fun _ => z)
    (fun _ a => (z a : ℝ) / scale a) g (Fintype.card A) le_rfl
    (Real.exp_nonneg _) hδ hg herr'
  have hj : (((∏ a, (scale a : ℝ)) *
      (dependentProductPMF (fun a => allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell
        (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c a))
        (fun a _ => z a)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [dependentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib,
      Complex.ofReal_prod]
  rw [hj]
  exact hp'

end Erdos3.VectorPolynomial

end

end OAI
