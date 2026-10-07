import OAI.Combinatorics.Progressions.Geometry.AllocatedInactiveNaturalSupport

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
theorem exists_allocated_inactive_natural_site_expansion
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hgamma : gamma ≤ 1) (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
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
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε + δ := by
  let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
  obtain ⟨F, hcard, hcap, hchar, hpoint⟩ := exists_allocated_inactive_natural_plateau_spectrum
    B U b S j i q hq r hsize hR hσ hgamma hsmall hlarge hcell hgrid A hA P ε hP hε hε1 rows hrows hB
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
    constantLaw (allocatedPrincipalGridScale_pos_of_radius B U b hR j i) radius rows F D a ω
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
  · intro x y hy
    let target : ℂ := (((scale : ℝ) ^ rows.card *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
        (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau supportRadius ((y u : ℝ) / scale) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hsupport
        (allocatedInactiveNaturalSites_bound B U b S j i q hq r hsize hR hσ
          hgamma hsmall hlarge hcell hgrid rows hrows x y hy hmass u)
    apply finite_site_cutoff_error target β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / scale))
      (fun u => scalarSupportPlateau supportRadius ((y u : ℝ) / scale))
      (show 0 ≤ ε + δ by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have hsite := he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have hp := hpoint x (fun t => booleanCoefficient y t)
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
theorem allocatedInactiveNaturalGrid_normalized_norm_le
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
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
    ‖(((scale : ℝ) ^ rows.card *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      max (cap + 1) ((smallHeight : ℝ) ^ rows.card) := by
  let : NeZero scale := ⟨(allocatedPrincipalGridScale_pos_of_radius B U b hR j i).ne'⟩
  rcases allocatedGridSide_natural_normalizable_or_bounded B U b hR S q j i hq hsize hgamma with hl | hs
  · obtain ⟨F, _, hcap, _, he⟩ := exists_allocated_inactive_natural_plateau_spectrum B U b S j i q hq r hl.2
      hR hσ hgamma hsmall hl.1 hcell hgrid A hA P 1 hP zero_lt_one le_rfl rows hrows hB
    have hb := allocatedInactiveNaturalPlateauApproximation_norm_le B U b S j i q hq r hl.2
      hR hσ (M := torus * scale) rfl rows z F hcap
    have ht := norm_sub_le_norm_sub_add_norm_sub
      ((((scale : ℝ) ^ rows.card *
        (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ))
      (allocatedInactiveNaturalPlateauApproximation B U b S j i q hq r hl.2 hR hσ (torus * scale) rows z F) 0
    simp only [sub_zero] at ht
    exact ((ht.trans (add_le_add (he x z) hb)).trans_eq (add_comm 1 cap)).trans (le_max_left _ _)
  · have hp : (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono (by simp) (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg)]
    exact ((mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg _) _) hp).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs) _)).trans (le_max_right _ _)

include hq in
theorem exists_allocated_inactive_natural_site_expansion_all_cases
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : height ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
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
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε + δ := by
  rcases allocatedGridSide_natural_normalizable_or_bounded B U b hR S q j i hq hsize hgamma with hl | hs
  · obtain ⟨e, he, herr⟩ := exists_allocated_inactive_natural_site_expansion B U b S j i q hq r hl.2
      hR hσ rows P ε hgamma hsmall hl.1 hcell hgrid A hA hP hε hε1 hrows hB hδ hQ
      ((add_le_add (le_max_left supportRadius shortRadius) (le_refl (1 / 4 : ℝ))).trans hHQ) hδQ hLQ
    exact ⟨e, he.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) le_rfl
      (add_le_add (le_max_left _ _) (le_refl (1 / 4 : ℝ))), herr⟩
  · obtain ⟨e, he, herr⟩ := exists_allocated_natural_bounded_grid_site_expansion B U b hR hσ S q r hcell j i
      hσ1 hgrid rows hs hδ hQ
      ((add_le_add (le_max_right supportRadius shortRadius) (le_refl (1 / 4 : ℝ))).trans hHQ)
      hshortCap hshortLip hshortError
    refine ⟨e, he.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) le_rfl
      (add_le_add (le_max_right _ _) (le_refl (1 / 4 : ℝ))), ?_⟩
    intro x y hy
    exact (herr x y hy).trans (le_add_of_nonneg_left hε.le)

end Erdos3.VectorPolynomial

end

end OAI
