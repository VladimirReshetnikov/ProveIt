import OAI.Combinatorics.Progressions.Geometry.AllocatedActiveSiteSupport
import OAI.Combinatorics.Progressions.Lattices.ResidueQuarterExtension
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridSiteFactors
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable {M : ℕ} [NeZero M] (rows : Finset (Finset α)) (P : ℝ)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "cap" => allocatedGridPointCap B P (Sigma.mk j i) rows
local notation "supportRadius" => allocatedNaturalSiteRadius (G := G) B j i rows

include hactive hq hsize in
theorem allocatedPhysicalGrid_normalized_norm_le
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
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((scale : ℝ) ^ rows.card *
      (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      cap + 1 := by
  have he := allocatedBudgetedPlateauApproximation_error B U basis hR hσ S q r j i
    hactive hq hsize hcell hgrid hgamma L hL P hcP hsP hM rows hrows hB
    (ε := 1) zero_lt_one le_rfl x z
  have hb := allocatedBudgetedPlateauApproximation_norm_le B U basis hR hσ S q r j i
    hactive hq hsize hgrid hgamma L hL P hcP hsP hM rows hrows hB 1 z
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (((scale : ℝ) ^ rows.card *
      (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x z).toReal : ℝ) : ℂ)
    (allocatedBudgetedPlateauApproximation B U basis hR hσ S q r j i hactive hq hsize P 1 M rows z) 0
  simp only [sub_zero] at ht
  exact (ht.trans (add_le_add he hb)).trans_eq (add_comm _ _)

variable (ε : ℝ)
local notation "bias" => positiveModerateRetainedBias j.val rows.card ((layerTailDegree m + 2) * rows.card)
  P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) ε
local notation "spectrum" => positiveModerateSpectrumCover rows M j.val P (torus : ℝ) S.value bias
local notation "freq" => Real.toNNReal (positiveRetainedFrequencyBound j.val rows.card P (torus : ℝ) bias)

include hactive hq hsize in
theorem exists_allocated_scalar_site_expansion
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
    (hε : 0 < ε) (hε1 : ε ≤ 1) {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : supportRadius + 1 / 4 ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        ((Finset.card spectrum) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (positiveRetainedDenominatorBound j.val rows.card ((layerTailDegree m + 2) * rows.card)
          P (torus : ℝ) ((2 * (torus : ℝ)) ^ rows.card) bias)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (supportRadius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε + δ := by
  obtain ⟨D, hD, hDb, N, _, hcard, β, f, hβ, hf, hLf, hsupp, he⟩ :=
    exists_allocated_supported_site_approximation B U basis hR hσ S q r j i hactive hq hsize rows P ε
      hcell hgrid hgamma L hL hcP hsP hM hrows hB hε hε1 hδ hQ hHQ hδQ hLQ
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α spectrum N
      period := fun k => D k.1
      coefficient := β
      factor := f }
  refine ⟨e, ⟨hcard, ?_, ?_, hβ, hf, hLf, hsupp⟩, ?_⟩
  · exact fun k => hD k.1
  · exact fun k => hDb k.1 k.1.property
  · exact fun x y hy => (he x y hy).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (P δ Q : ℝ)
variable (M : A → ℕ) [∀ a, NeZero (M a)]

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "torus" => fun a : A => allocatedGridTorusFactor B α (selected a)
local notation "cap" => fun a : A => allocatedGridPointCap B P (selected a) ((rows) a)
local notation "trueCap" => allocatedGridFamilyCap B rowFamily P + 1
local notation "accuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap δ
local notation "halfAccuracy" => accuracy / 2
local notation "bias" => fun a : A => positiveModerateRetainedBias (Fin.val (Sigma.fst (selected a)))
  (Finset.card ((rows) a)) ((layerTailDegree m + 2) * (Finset.card ((rows) a))) P ((torus) a : ℝ)
  ((2 * ((torus) a : ℝ)) ^ (Finset.card ((rows) a))) halfAccuracy
local notation "spectrum" => fun a : A => positiveModerateSpectrumCover ((rows) a) (M a)
  (Fin.val (Sigma.fst (selected a))) P ((torus) a : ℝ) S.value ((bias) a)
local notation "freq" => fun a : A => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (selected a))) (Finset.card ((rows) a)) P ((torus) a : ℝ) ((bias) a))
local notation "radius" => fun a : A => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (selected a)) (Sigma.snd (selected a)) ((rows) a)

theorem exists_allocated_joint_site_expansion
    (hP : 1 ≤ P) (hδ : 0 < δ) (hQ : 0 ≤ Q) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hHQ : ∀ a, (radius) a + 1 / 4 ≤ Real.exp Q)
    (hδQ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ∀ a, ((CircleFourier.characterLipConstant * (((rows) a).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    ∃ e : A → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds
        ((Finset.card ((spectrum) a)) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (positiveRetainedDenominatorBound (selected a).1.val ((rows) a).card
          ((layerTailDegree m + 2) * ((rows) a).card) P ((torus) a : ℝ)
          ((2 * ((torus) a : ℝ)) ^ ((rows) a).card) ((bias) a))
        ((cap) a * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) ((radius) a + 1 / 4)) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → A → ℤ),
        (∀ a t, t ∉ (rows) a → booleanCoefficient (fun s => y s a) t = 0) →
        ‖(((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
            (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x
              (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
          siteFamilyEval e y (fun s a => (y s a : ℝ) / (axisN) a)‖ ≤ δ := by
  have hcap : 0 ≤ trueCap := by
    have hc := allocatedGridFamilyCap_nonneg B rowFamily hP
    linarith
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec
    (Fintype.card (Σ j : Fin m, Fin (n j))) hcap hδ
  have hhalf : 0 < halfAccuracy := half_pos hτ
  have hhalf1 : halfAccuracy ≤ 1 := by linarith
  have heach (a : A) := exists_allocated_scalar_site_expansion B U basis hR hσ S q r
    (selected a).1 (selected a).2 (hactive a) hq hsize ((rows) a) P halfAccuracy hcell (hgrid a)
    (hgamma a) L hL hcP hsP (hM a) (hrows a) (hB a) hhalf hhalf1
    hhalf hQ (hHQ a) (hδQ a) (hLQ a)
  choose e hb he using heach
  refine ⟨e, hb, ?_⟩
  intro x y hy
  let g (a : A) : ℂ := (((axisN) a : ℝ) ^ ((rows) a).card *
    (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell (selected a).1 (selected a).2
      ((rows) a) x (fun t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ)
  have hg (a : A) : ‖g a‖ ≤ trueCap := by
    apply (allocatedPhysicalGrid_normalized_norm_le B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize ((rows) a) P hcell (hgrid a)
      (hgamma a) L hL hcP hsP (hM a) (hrows a) (hB a) x _).trans
    exact add_le_add (allocatedGridPointCap_le_family B rowFamily hP (selected a)) (le_rfl : (1 : ℝ) ≤ 1)
  have herr (a : A) : ‖g a - (e a).eval (fun s => y s a) (fun s => (y s a : ℝ) / (axisN) a)‖ ≤
      accuracy := by
    have h := he a x (fun s => y s a) (hy a)
    simpa only [ScalarSiteExpansion.integerEval, g, add_halves] using h
  have hp := siteFamily_approximation e y (fun s a => (y s a : ℝ) / (axisN) a) g
    (Fintype.card (Σ j : Fin m, Fin (n j))) (Fintype.card_le_of_injective selected hselected)
    hcap hδ hg herr
  have hj : (((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
      (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x
        (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [allocatedSupportedPhysicalGrid_joint_mass B U basis hR hσ S q r hcell
      selected (rows) x hselected hgrid _, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [hj]
  exact hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem allocatedActiveSiteApproximation_error
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε : ℝ}
    (he : ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → activeAxes → ℤ),
      (∀ a t, t ∉ rowSets (ig a.val).1 → booleanCoefficient (fun s => y s a) t = 0) →
      ‖(((∏ a : activeAxes, (axisN a.val : ℝ) ^ (rowSets (ig a.val).1).card) *
          (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell
            (fun a : activeAxes => ig a.val) (fun a => rowSets (ig a.val).1) x
            (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
        siteFamilyEval e y (fun s a => (y s a : ℝ) / axisN a.val)‖ ≤ ε)
    (x : G → IntegerScalarCubeBox α S.value)
    (z : (a : activeAxes) → CoefficientJetAxisRow (rowTypes) a.val.val) :
    ‖(allocatedActiveNaturalVolume B U b S rowSets : ℂ) *
        ((∏ a : activeAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell
          a.val (z a)).toReal : ℝ) : ℂ) -
      allocatedActiveSiteApproximation B U b S rowSets e z‖ ≤ ε := by
  let y := allocatedActiveSiteValues B U b S rowSets z
  have hc (a : activeAxes) (t : rowSets (ig a.val).1) :
      booleanCoefficient (fun s => y s a) t.val =
        allocatedGridIntegerValues B U b S rowSets a.val (z a) t :=
    integerBooleanSitesFromRows_coefficient_mem _ _ t
  have hy (a : activeAxes) (t : Finset α) (ht : t ∉ rowSets (ig a.val).1) :
      booleanCoefficient (fun s => y s a) t = 0 :=
    integerBooleanSitesFromRows_coefficient_outside _ _ t ht
  have hmass : (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell
      (fun a : activeAxes => ig a.val) (fun a => rowSets (ig a.val).1) x
      (fun a t => booleanCoefficient (fun s => y s a) t)).toReal =
      ∏ a : activeAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell a.val (z a)).toReal := by
    rw [allocatedSupportedPhysicalGrid_joint_mass B U b hR hσ S q r hcell
      (fun a : activeAxes => ig a.val) (fun a => rowSets (ig a.val).1) x
      ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective)
      (fun a => allocatedGridIntegerAxis_grid B U b S a.val)]
    apply Finset.prod_congr rfl
    intro a _
    rw [allocatedSupportedGridJetPMF_integer B U b hR hσ S rowSets x q r hcell]
    apply congrArg (fun v : rowSets (ig a.val).1 → ℤ =>
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell
        (ig a.val).1 (ig a.val).2 (rowSets (ig a.val).1) x v).toReal)
    funext t
    exact hc a t
  have h := he x y hy
  rw [hmass, Complex.ofReal_mul] at h
  exact h

variable (P ε Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap ε / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B α (ig (Subtype.val a)))
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "spectrum" => (fun a : activeAxes => positiveModerateSpectrumCover (rowSets (Sigma.fst (ig (Subtype.val a)))) (M a)
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) P ((torus) a : ℝ) S.value ((bias) a))

noncomputable def allocatedActiveSiteBounds
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) : Prop :=
  ∀ a, (e a).Bounds
    (Finset.card ((spectrum) a) * Real.exp (Fintype.card (Finset α) * (4 * Λ + 8)))
    (positiveRetainedDenominatorBound (ig a.val).1.val (rowSets (ig a.val).1).card
      ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) P ((torus) a : ℝ)
      ((2 * ((torus) a : ℝ)) ^ (rowSets (ig a.val).1).card) ((bias) a))
    (allocatedGridPointCap B P (ig a.val) (rowSets (ig a.val).1) *
      Real.exp (Fintype.card (Finset α) * (4 * Λ + 8) + Λ))
    (⟨Real.exp (1 + 6 * Λ + 12), Real.exp_nonneg _⟩ + 4)
    (allocatedNaturalSiteRadius (G := G) B (ig a.val).1 (ig a.val).2 (rowSets (ig a.val).1) + 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

def allocatedGridRowFromIntegerValues (a : gridAxes) (z : rowSets (ig a).1 → ℤ) :
    CoefficientJetAxisRow (rowTypes) a.val := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact z

omit [Fintype α] [DecidableEq α] in
theorem allocatedGridIntegerValues_fromValues (a : gridAxes) (z : rowSets (ig a).1 → ℤ) :
    allocatedGridIntegerValues B U b S rowSets a (allocatedGridRowFromIntegerValues B U b S rowSets a z) = z := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

omit [Fintype α] [DecidableEq α] in
theorem allocatedGridRowFromIntegerValues_inverse (a : gridAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val) :
    allocatedGridRowFromIntegerValues B U b S rowSets a (allocatedGridIntegerValues B U b S rowSets a z) = z := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

noncomputable def allocatedActiveRowsFromSites (y : Finset α → activeAxes → ℤ)
    (a : activeAxes) : CoefficientJetAxisRow (rowTypes) a.val.val :=
  allocatedGridRowFromIntegerValues B U b S rowSets a.val
    (fun t => booleanCoefficient (fun s => y s a) t.val)

theorem allocatedActiveSiteValues_rowsFromSites (y : Finset α → activeAxes → ℤ)
    (hy : ∀ a t, t ∉ rowSets (ig a.val).1 → booleanCoefficient (fun s => y s a) t = 0) :
    allocatedActiveSiteValues B U b S rowSets (allocatedActiveRowsFromSites B U b S rowSets y) = y := by
  funext s a
  unfold allocatedActiveSiteValues allocatedActiveRowsFromSites
  rw [allocatedGridIntegerValues_fromValues]
  exact congrFun (integerBooleanSitesFromRows_eq (rowSets (ig a.val).1) (fun s => y s a) (hy a)) s

theorem allocatedActiveSiteApproximation_rowsFromSites
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (y : Finset α → activeAxes → ℤ)
    (hy : ∀ a t, t ∉ rowSets (ig a.val).1 → booleanCoefficient (fun s => y s a) t = 0) :
    allocatedActiveSiteApproximation B U b S rowSets e (allocatedActiveRowsFromSites B U b S rowSets y) =
      siteFamilyEval e y (fun s a => (y s a : ℝ) / axisN a.val) := by
  unfold allocatedActiveSiteApproximation
  rw [allocatedActiveSiteValues_rowsFromSites B U b S rowSets y hy]

theorem allocatedActiveSiteApproximation_affine
    (e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {K : Type*} [Fintype K]
    (root : activeAxes → K → ℤ) (dirs : activeAxes → Matrix α K ℤ)
    (c : ∀ a : activeAxes, BoundedCoefficientExponent K ((ig a.val).1.val + 1) → ℤ)
    (hrows : ∀ (j : Fin m) (t : Finset α), t.card ≤ j.val + 1 → t ∈ rowSets j) :
    let y := fun s a => (boundedSiteMatrix ((ig a.val).1.val + 1)
      (integerAffineCube (root a) (dirs a)) *ᵥ c a) s
    allocatedActiveSiteApproximation B U b S rowSets e (allocatedActiveRowsFromSites B U b S rowSets y) =
      siteFamilyEval e y (fun s a => (y s a : ℝ) / axisN a.val) := by
  dsimp only
  apply allocatedActiveSiteApproximation_rowsFromSites B U b S rowSets e
  intro a
  exact bounded_affine_site_coefficients_outside_rows (root a) (dirs a) ((ig a.val).1.val + 1)
    (rowSets (ig a.val).1) (hrows (ig a.val).1) (c a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))

local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J
local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_periodic_ambient_site_factor (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (D : ℝ≥0) (hD : ∀ a, V a ≤ D)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (k : ∀ a, (e a).Term) (s : S) :
    ∃ g : (A → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
      LipschitzWith (4 * max ((((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)))) (2 * D)) g ∧
      (∀ z, ‖g z‖ ≤ 4) ∧
      ∀ (y : A → ℤ) (v : ambient → ℝ), (∀ i, |v i| ≤ 1 / 4) →
        g ((fun a => (((y a : ℝ) / (e a).period (k a) : ℝ) : UnitAddCircle)),
          (fun i => (v i : UnitAddCircle))) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
          (fun a => (y a : ZMod ((e a).period (k a))))
          (allocatedFullAmbientSiteCoordinates (R := R) U b o v) := by
  let : ∀ a, NeZero ((e a).period (k a)) := fun a => ⟨((h a).period_pos (k a)).ne'⟩
  let F := fun (r : ∀ a, ZMod ((e a).period (k a))) (v : ambient → ℝ) =>
    allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r
      (allocatedFullAmbientSiteCoordinates (R := R) U b o v)
  have hF (r : ∀ a, ZMod ((e a).period (k a))) :=
    ((allocatedFullGridSiteFactor_bounds B U b e selected hR h Q hQ k s r).2).comp
      (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK)
  have hb (r : ∀ a, ZMod ((e a).period (k a))) (v : ambient → ℝ) : ‖F r v‖ ≤ 1 :=
    (allocatedFullGridSiteFactor_bounds B U b e selected hR h Q hQ k s r).1 _
  obtain ⟨g, hg, hgb, hgv⟩ := exists_residue_quarter_extension (fun a => (e a).period (k a))
    D ((((Fintype.card A * L) * Q) * (K * ∑ j, Cforward j * Fintype.card (J j))))
    (fun a => ((h a).period_le (k a)).trans (hD a)) F hF hb
  refine ⟨g, hg, hgb, ?_⟩
  intro y v hv
  have hvalue := hgv (fun a => (y a : ZMod ((e a).period (k a)))) v hv
  change g ((fun a => ZMod.toAddCircle (y a : ZMod ((e a).period (k a)))),
    fun i => (v i : UnitAddCircle)) = F (fun a => (y a : ZMod ((e a).period (k a)))) v at hvalue
  simpa only [ZMod.toAddCircle_intCast] using hvalue

theorem allocatedPeriodicAmbientSiteFactor_chart (hR : ∀ j, 0 < R j)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (k : ∀ a, (e a).Term) (s : S)
    (g : (A → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ)
    (hg : ∀ (y : A → ℤ) (v : ambient → ℝ), (∀ i, |v i| ≤ 1 / 4) →
      g ((fun a => (((y a : ℝ) / (e a).period (k a) : ℝ) : UnitAddCircle)),
        (fun i => (v i : UnitAddCircle))) =
      allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
        (fun a => (y a : ZMod ((e a).period (k a))))
        (allocatedFullAmbientSiteCoordinates (R := R) U b o v))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) :
    g ((fun a => (((((z.1 (selected a).1).2 (selected a).2 () : ℤ) : ℝ) /
          (e a).period (k a) : ℝ) : UnitAddCircle)),
        coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
      siteFamilyFactor e k s
        (fun a => ((z.1 (selected a).1).2 (selected a).2 () : ZMod ((e a).period (k a))))
        (fun a => (((z.1 (selected a).1).2 (selected a).2 () : ℤ) : ℝ) / (scale) a) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ i, |mixedJetAmbientPoint U b o z.1 i| ≤ 1 / 4 := by
    rintro ⟨j, t, i⟩
    exact (hz j (Set.mem_univ j) t (Set.mem_univ t)).1 i
  rw [hg _ _ hsmall, allocatedFullAmbientSiteCoordinates_point,
    allocatedFullGridSiteFactor_point B U b e selected hR k s]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem lipschitz_complex_div_four {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (K : ℝ≥0) (hf : LipschitzWith (4 * K) f) :
    LipschitzWith K (fun x => f x / 4) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_div, norm_div]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h := hf.dist_le_mul x y
  simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] at h
  nlinarith only [h]

theorem complex_div_four_norm_le {z : ℂ} (hz : ‖z‖ ≤ 4) : ‖z / 4‖ ≤ 1 := by
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [norm_div, h4]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by simpa using hz)

theorem four_scaled_product_identity {S : Type*} [Fintype S] (c : ℂ) (f : S → ℂ) :
    ((4 : ℂ) ^ Fintype.card S * c) * (∏ s, f s / 4) = c * ∏ s, f s := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  have h4 : (4 : ℂ) ^ Fintype.card S ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [h4]

attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def periodicAmbientSiteCoefficient {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) (k : ∀ a, (e a).Term) : ℂ :=
  (4 : ℂ) ^ Fintype.card S * siteFamilyCoefficient e k

theorem periodicAmbientSiteCoefficient_bound {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) :
    (∑ k, ‖periodicAmbientSiteCoefficient e k‖) ≤ (4 : ℝ) ^ Fintype.card S * ∏ a, C a := by
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  simp only [periodicAmbientSiteCoefficient, norm_mul, norm_pow, h4, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (siteFamily_coefficient_le e h) (by positivity)

namespace VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))

local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J
local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_periodic_ambient_site_expansion (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (D : ℝ≥0) (hD : ∀ a, V a ≤ D)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] :
    ∃ g : (∀ a, (e a).Term) → S → (A → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
      (∀ k s, LipschitzWith (max ((((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)))) (2 * D)) (g k s) ∧
        ∀ p, ‖g k s p‖ ≤ 1) ∧
      ∀ z : S → MixedCoveredJetSource I (fun _ : Fin m => Unit) E n d,
        (∀ s, z s ∈ mixedCoveredJetRegion U o b d
          (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))) →
        (∑ k, periodicAmbientSiteCoefficient e k * ∏ s,
          g k s ((fun a => (↑((((z s).1 (selected a).1).2 (selected a).2 () : ℝ) /
              (e a).period (k a)) : UnitAddCircle)),
            coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d (z s)))) =
        siteFamilyEval e (fun s a => ((z s).1 (selected a).1).2 (selected a).2 ())
          (fun s a => ((((z s).1 (selected a).1).2 (selected a).2 () : ℤ) : ℝ) / (scale) a) := by
  have heach (k : ∀ a, (e a).Term) (s : S) :=
    exists_allocated_periodic_ambient_site_factor B U b e selected hR h Q hQ D hD o Cforward hforward K hK k s
  choose raw hLip hNorm hValue using heach
  let g := fun k s p => raw k s p / 4
  refine ⟨g, ?_, ?_⟩
  · intro k s
    exact ⟨lipschitz_complex_div_four (raw k s) _ (hLip k s),
      fun p => complex_div_four_norm_le (hNorm k s p)⟩
  · intro z hz
    have hv (k : ∀ a, (e a).Term) (s : S) :=
      allocatedPeriodicAmbientSiteFactor_chart B U b e selected hR o k s (raw k s) (hValue k s)
        hb bW d (z s) (hz s)
    dsimp only [g]
    simp_rw [hv]
    unfold siteFamilyEval periodicAmbientSiteCoefficient
    apply Finset.sum_congr rfl
    intro k _
    exact four_scaled_product_identity (siteFamilyCoefficient e k) _

end VectorPolynomial
end Erdos3

end

end OAI
