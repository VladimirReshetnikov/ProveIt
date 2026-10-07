import OAI.Combinatorics.Progressions.Probability.ConditionalWindowIntegral
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (x : G → IntegerScalarCubeBox α S.value)
variable (P δ : ℝ)

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "accuracy" => allocatedGridFamilyAccuracy B rowFamily P δ

theorem allocatedJointPlateau_family_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (z : ∀ a, (rows) a → ℤ) :
    ‖(((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
        (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z).toReal : ℝ) : ℂ) -
      ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
        (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)‖ ≤ δ := by
  let f (a : A) : ℂ := (((axisN) a : ℝ) ^ ((rows) a).card *
    (allocatedSupportedPhysicalGridPMF B U basis hR hσ S q r hcell
      (selected a).1 (selected a).2 ((rows) a) x (z a)).toReal : ℝ)
  let g (a : A) : ℂ := allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
    (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)
  obtain ⟨hε, hε1⟩ := allocatedGridFamilyAccuracy_spec B rowFamily hP hδ
  have hg (a : A) : ‖g a‖ ≤ allocatedGridFamilyCap B rowFamily P :=
    (allocatedBudgetedPlateauApproximation_norm_le B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize (hgrid a) (hgamma a)
      L hL P hcP hsP (hM a) ((rows) a) (hrows a) (hB a) accuracy (z a)).trans
      (allocatedGridPointCap_le_family B rowFamily hP (selected a))
  have herr (a : A) : ‖f a - g a‖ ≤ accuracy :=
    allocatedBudgetedPlateauApproximation_error B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize hcell (hgrid a) (hgamma a)
      L hL P hcP hsP (hM a) ((rows) a) (hrows a) (hB a) hε hε1 x (z a)
  have hp := norm_prod_sub_prod_le_uniform_accuracy (Fintype.card (Σ j : Fin m, Fin (n j)))
    (Fintype.card_le_of_injective selected hselected)
    (allocatedGridFamilyCap_nonneg B rowFamily hP) hδ f g hg herr
  have hj : (((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
      (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z).toReal : ℝ) : ℂ) =
      ∏ a, f a := by
    rw [allocatedSupportedPhysicalGrid_joint_mass B U basis hR hσ S q r hcell
      selected (rows) x hselected hgrid z, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  exact (congrArg (fun v : ℂ => ‖v - ∏ a, g a‖) hj).trans_le hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (x : G → IntegerScalarCubeBox α S.value)
variable (P δ : ℝ)

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "accuracy" => allocatedGridFamilyAccuracy B rowFamily P δ

local notation "axisRadius" => fun a : A => allocatedNaturalSupportRadius (G := G) B α
  (Sigma.fst (selected a)) (Sigma.snd (selected a))

noncomputable def allocatedSelectedNaturalWindow : Finset (∀ a, (rows) a → ℤ) :=
  naturalScaleProductWindow (fun a => (rows) a) (axisRadius) (axisN)

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedSelectedNaturalWindow_outside (z : ∀ a, (rows) a → ℤ)
    (hz : z ∉ allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected) :
    ∃ a, ¬∀ t, |(z a t : ℝ)| ≤ (axisRadius) a * (axisN) a := by
  have hn : ¬∀ a, z a ∈ naturalScaleIntegerWindow ((rows) a) ((axisRadius) a) ((axisN) a) := by
    simpa only [allocatedSelectedNaturalWindow, mem_naturalScaleProductWindow_iff] using hz
  obtain ⟨a, ha⟩ := not_forall.mp hn
  exact ⟨a, fun h => ha (mem_naturalScaleIntegerWindow_of_bound _ _ _ h)⟩

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
include hR in
theorem allocatedSelectedNaturalWindow_card_le
    (hselected : Function.Injective selected)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a) :
    ((allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected).card : ℝ) ≤
      allocatedGridFamilyWindowVolume (G := G) B rowFamily *
        ∏ a, ((axisN) a : ℝ) ^ ((rows) a).card := by
  have hc := naturalScaleProductWindow_card_le (fun a => (rows) a) (axisRadius) (axisN)
    (fun a => allocatedNaturalSupportRadius_nonneg (G := G) B α (selected a).1 (selected a).2)
    (fun a => allocatedPrincipalGridScale_pos B U basis hR S (selected a).1 (selected a).2 (hactive a))
  simp only [Fintype.card_coe] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (allocatedSelectedWindowVolume_le (G := G) B rowFamily selected hselected) (by positivity))

theorem allocatedJointPhysical_zero_off_window
    (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (z : ∀ a, (rows) a → ℤ)
    (hz : z ∉ allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected) :
    allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z = 0 := by
  rw [allocatedSupportedPhysicalGrid_joint_law B U basis hR hσ S q r hcell
    selected (rows) x hselected hgrid, dependentProductPMF_apply]
  obtain ⟨a, ha⟩ := allocatedSelectedNaturalWindow_outside (G := G) B U basis rowFamily selected z hz
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (allocatedNaturalPhysicalPoint_zero_off_window B U basis hR hσ S
      (selected a).1 (selected a).2 (hactive a) q r hq hsize hcell (hgrid a)
      ((rows) a) (hrows a) x (z a) ha)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedJointPlateau_zero_off_window
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (ε : ℝ) (M : A → ℕ) [∀ a, NeZero (M a)] (z : ∀ a, (rows) a → ℤ)
    (hz : z ∉ allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected) :
    (∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize P ε (M a) ((rows) a) (z a)) = 0 := by
  obtain ⟨a, ha⟩ := allocatedSelectedNaturalWindow_outside (G := G) B U basis rowFamily selected z hz
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (allocatedBudgetedPlateau_zero_off_window B U basis hR hσ S
      (selected a).1 (selected a).2 (hactive a) q r hq hsize P ε (M a) ((rows) a) (z a) ha)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (x : G → IntegerScalarCubeBox α S.value)
variable (P δ : ℝ)

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
noncomputable def allocatedGridL1PointTolerance : ℝ :=
  δ / (allocatedGridFamilyWindowVolume (G := G) B rowFamily + 1)

local notation "pointTolerance" => allocatedGridL1PointTolerance (G := G) B rowFamily δ
local notation "accuracy" => allocatedGridFamilyAccuracy B rowFamily P pointTolerance

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedGridL1PointTolerance_spec (hδ : 0 < δ) :
    0 < pointTolerance ∧ pointTolerance * allocatedGridFamilyWindowVolume (G := G) B rowFamily ≤ δ := by
  have hV := allocatedGridFamilyWindowVolume_nonneg (G := G) B rowFamily
  have hp : 0 < pointTolerance := div_pos hδ (by linarith)
  refine ⟨hp, ?_⟩
  calc
    _ ≤ pointTolerance * (allocatedGridFamilyWindowVolume (G := G) B rowFamily + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hp.le
    _ = δ := by unfold allocatedGridL1PointTolerance; field_simp

theorem allocatedJointPlateau_family_l1_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    : (∑' z : ∀ a, (rows) a → ℤ,
      ‖((allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z).toReal : ℂ) -
        (∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)) /
            ((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card : ℝ) : ℂ)‖) ≤ δ := by
  let N : ℝ := ∏ a, ((axisN) a : ℝ) ^ ((rows) a).card
  let f (z : ∀ a, (rows) a → ℤ) : ℂ :=
    (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z).toReal
  let g (z : ∀ a, (rows) a → ℤ) : ℂ :=
    ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)
  let W := allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected
  have hN : 0 < N := Finset.prod_pos (fun a _ => pow_pos
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos B U basis hR S
      (selected a).1 (selected a).2 (hactive a))) _)
  have hτ := allocatedGridL1PointTolerance_spec (G := G) B rowFamily δ hδ
  have hpoint (z : ∀ a, (rows) a → ℤ) : ‖(N : ℂ) * f z - g z‖ ≤ pointTolerance := by
    have he := allocatedJointPlateau_family_error B U basis hR hσ S q r hcell rowFamily selected x P
      pointTolerance hP hτ.1 hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB z
    simpa only [f, g, N, Complex.ofReal_mul] using he
  have hzero (z : ∀ a, (rows) a → ℤ) (hz : z ∉ W) : f z = 0 ∧ g z = 0 := by
    constructor
    · dsimp only [f]
      rw [allocatedJointPhysical_zero_off_window B U basis hR hσ S q r hcell
        rowFamily selected x hselected hgrid hactive hq hsize hrows z hz,
        ENNReal.toReal_zero, Complex.ofReal_zero]
    · exact allocatedJointPlateau_zero_off_window B U basis hR hσ S q r rowFamily selected P
        hactive hq hsize accuracy M z hz
  have hc : (W.card : ℝ) ≤ allocatedGridFamilyWindowVolume (G := G) B rowFamily * N :=
    allocatedSelectedNaturalWindow_card_le B U basis hR S rowFamily selected hselected hactive
  exact (finite_window_normalized_l1_error W f g hN hτ.1.le hc hzero hpoint).trans hτ.2

theorem allocatedJointPlateau_family_test_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (test : (∀ a, (rows) a → ℤ) → ℂ) (htest : ∀ z, ‖test z‖ ≤ 1) :
    ‖∑' z : ∀ a, (rows) a → ℤ,
      (((allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z).toReal : ℂ) -
        (∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
          (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)) /
            ((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card : ℝ) : ℂ)) * test z‖ ≤ δ := by
  let N : ℝ := ∏ a, ((axisN) a : ℝ) ^ ((rows) a).card
  let f (z : ∀ a, (rows) a → ℤ) : ℂ :=
    (allocatedSupportedPhysicalJointPMF B U basis hR hσ S q r hcell selected (rows) x z).toReal
  let g (z : ∀ a, (rows) a → ℤ) : ℂ :=
    ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
      (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)
  let W := allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected
  have hN : 0 < N := Finset.prod_pos (fun a _ => pow_pos
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos B U basis hR S
      (selected a).1 (selected a).2 (hactive a))) _)
  have hτ := allocatedGridL1PointTolerance_spec (G := G) B rowFamily δ hδ
  have hpoint (z : ∀ a, (rows) a → ℤ) : ‖(N : ℂ) * f z - g z‖ ≤ pointTolerance := by
    have he := allocatedJointPlateau_family_error B U basis hR hσ S q r hcell rowFamily selected x P
      pointTolerance hP hτ.1 hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB z
    simpa only [f, g, N, Complex.ofReal_mul] using he
  have hzero (z : ∀ a, (rows) a → ℤ) (hz : z ∉ W) : f z = 0 ∧ g z = 0 := by
    constructor
    · dsimp only [f]
      rw [allocatedJointPhysical_zero_off_window B U basis hR hσ S q r hcell
        rowFamily selected x hselected hgrid hactive hq hsize hrows z hz,
        ENNReal.toReal_zero, Complex.ofReal_zero]
    · exact allocatedJointPlateau_zero_off_window B U basis hR hσ S q r rowFamily selected P
        hactive hq hsize accuracy M z hz
  have hc : (W.card : ℝ) ≤ allocatedGridFamilyWindowVolume (G := G) B rowFamily * N :=
    allocatedSelectedNaturalWindow_card_le B U basis hR S rowFamily selected hselected hactive
  exact (finite_window_normalized_test_error W f g test hN hτ.1.le hc hzero hpoint htest).trans hτ.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell

variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P ε : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

noncomputable def allocatedActivePlateauProduct (z : ((a : activeAxes) → CoefficientJetAxisRow (rowTypes) (Subtype.val (Subtype.val a)))) : ℂ :=
  ∏ a, allocatedActivePlateauAxis B U b hR hσ S rowSets q r hq hsize P ε M a (z a)

theorem allocatedActivePlateauProduct_zero
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (z : ((a : activeAxes) → CoefficientJetAxisRow (rowTypes) (Subtype.val (Subtype.val a)))) (hz : ∃ a, z a ∉ allocatedGridNaturalWindow B U b S rowSets a.val) :
    (∏ a, (laws a.val (z a)).toReal) = 0 ∧
      allocatedActivePlateauProduct B U b hR hσ S rowSets q r hq hsize P ε M z = 0 := by
  obtain ⟨a, ha⟩ := hz
  have h := allocatedActivePlateauAxis_zero B U b hR hσ S rowSets x q r hcell hq hsize P ε M hrows a (z a) ha
  exact ⟨Finset.prod_eq_zero (Finset.mem_univ a) h.1, Finset.prod_eq_zero (Finset.mem_univ a) h.2⟩

variable (δ : ℝ)
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))
local notation "accuracy" => allocatedGridFamilyAccuracy B (rowFamily) P δ

theorem allocatedActivePlateauProduct_error
    (hP : 1 ≤ P) (hδ : 0 < δ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (ig a.val) * axisN a.val)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (z : ((a : activeAxes) → CoefficientJetAxisRow (rowTypes) (Subtype.val (Subtype.val a)))) :
    ‖(allocatedActiveNaturalVolume B U b S rowSets : ℂ) *
        ((∏ a, (laws a.val (z a)).toReal : ℝ) : ℂ) -
      allocatedActivePlateauProduct B U b hR hσ S rowSets q r hq hsize P accuracy M z‖ ≤ δ := by
  obtain ⟨hε, hε1⟩ := allocatedGridFamilyAccuracy_spec B (rowFamily) hP hδ
  have ha (a : activeAxes) := allocatedActivePlateauAxis_estimates B U b hR hσ S rowSets x q r hcell
    hq hsize P accuracy M hgamma L hL hcP hsP hM hrows hB hε hε1 a (z a)
  let F (a : activeAxes) : ℂ := (((axisN a.val : ℝ) ^ (rowSets (ig a.val).1).card *
    (laws a.val (z a)).toReal : ℝ) : ℂ)
  let H (a : activeAxes) : ℂ := allocatedActivePlateauAxis B U b hR hσ S rowSets q r hq hsize P accuracy M a (z a)
  have hH (a : activeAxes) : ‖H a‖ ≤ allocatedGridFamilyCap B (rowFamily) P :=
    (ha a).1.trans (allocatedGridPointCap_le_family B (rowFamily) hP (ig a.val))
  have herr := norm_prod_sub_prod_le_uniform_accuracy (Fintype.card (Σ j : Fin m, Fin (n j)))
    (Fintype.card_le_of_injective (fun a : activeAxes => ig a.val)
      ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective))
    (allocatedGridFamilyCap_nonneg B (rowFamily) hP) hδ F H hH (fun a => (ha a).2)
  have heq : (allocatedActiveNaturalVolume B U b S rowSets : ℂ) *
      ((∏ a, (laws a.val (z a)).toReal : ℝ) : ℂ) = ∏ a, F a := by
    unfold allocatedActiveNaturalVolume
    rw [← Complex.ofReal_mul, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  exact (congrArg (fun v : ℂ => ‖v - ∏ a, H a‖) heq).trans_le herr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ)

local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)

variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (x : G → IntegerScalarCubeBox α S.value)
variable (P δ : ℝ)

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "pointTolerance" => allocatedGridL1PointTolerance (G := G) B rowFamily δ
local notation "accuracy" => allocatedGridFamilyAccuracy B rowFamily P pointTolerance

local notation "jointLaw" => fun y => dependentProductPMF (fun a : A =>
  integerMatrixImagePMF (boundedCoefficientJetMatrix
    (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U basis S x y) ((Fin.val (Sigma.fst (selected a))) + 1)
    (fun t : (rows) a => (t : Finset α)))
    (allocatedLayerIntegerPMFs B U basis hR hσ S (Sigma.fst (selected a)) (Sigma.snd (selected a))))

noncomputable def allocatedJointNaturalVolume : ℝ :=
  ∏ a, ((axisN) a : ℝ) ^ ((rows) a).card

noncomputable def allocatedJointPhysicalKernel :
    PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
      PMF (∀ a, (rows) a → ℤ) := jointLaw

noncomputable def allocatedJointPlateauProduct
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (z : ∀ a, (rows) a → ℤ) : ℂ :=
  ∏ a, allocatedBudgetedPlateauApproximation B U basis hR hσ S q r
    (selected a).1 (selected a).2 (hactive a) hq hsize P accuracy (M a) ((rows) a) (z a)

local notation "volumeN" => allocatedJointNaturalVolume (G := G) B U basis (R := R) rowFamily selected
local notation "kernel" => allocatedJointPhysicalKernel B U basis hR hσ S rowFamily selected x

theorem allocatedJointWindow_data_support
    (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hr : 0 < (tuples).mass (Finset.univ.filter (fun v => principalResidueLabel q v = r)))
    (v : ∀ a, (rows) a → ℤ)
    (hv : v ∉ allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected) :
    (((tuples).condition _ hr).toPMF.bind kernel) v = 0 ∧
      allocatedJointPlateauProduct B U basis hR hσ S q rowFamily selected P δ hactive hq hsize M r v = 0 := by
  constructor
  · exact allocatedJointPhysical_zero_off_window B U basis hR hσ S q r hr
      rowFamily selected x hselected hgrid hactive hq hsize hrows v hv
  · exact allocatedJointPlateau_zero_off_window B U basis hR hσ S q r rowFamily selected P
      hactive hq hsize accuracy M v hv

theorem allocatedJointWindow_data_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hr : 0 < (tuples).mass (Finset.univ.filter (fun v => principalResidueLabel q v = r)))
    (v : ∀ a, (rows) a → ℤ) :
    ‖(volumeN : ℂ) * (((((tuples).condition _ hr).toPMF.bind kernel) v).toReal : ℂ) -
      allocatedJointPlateauProduct B U basis hR hσ S q rowFamily selected P δ hactive hq hsize M r v‖ ≤
      pointTolerance := by
  have hτ := (allocatedGridL1PointTolerance_spec (G := G) B rowFamily δ hδ).1
  have he := allocatedJointPlateau_family_error B U basis hR hσ S q r hr rowFamily selected x P
    pointTolerance hP hτ hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB v
  unfold allocatedJointPhysicalKernel
  simpa only [allocatedSupportedPhysicalJointPMF, allocatedJointPlateauProduct,
    allocatedJointNaturalVolume, Complex.ofReal_mul] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) [NeZero q]

local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)

variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (x : G → IntegerScalarCubeBox α S.value)
variable (P δ : ℝ)

local notation "rows" => fun a : A => rowFamily (selected a)
local notation "axisK" => fun a : A => basisAxisScale (basis (Sigma.fst (selected a))) (Sigma.snd (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U basis (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "axisGamma" => fun a : A => principalProfileSize (R (Sigma.fst (selected a)))
  (Finset.card (layerIntegerPrincipalSlots (G := G) B (Sigma.fst (selected a)) (Sigma.snd (selected a))))
local notation "pointTolerance" => allocatedGridL1PointTolerance (G := G) B rowFamily δ
local notation "accuracy" => allocatedGridFamilyAccuracy B rowFamily P pointTolerance

local notation "volumeN" => allocatedJointNaturalVolume (G := G) B U basis (R := R) rowFamily selected
local notation "kernel" => allocatedJointPhysicalKernel B U basis hR hσ S rowFamily selected x

theorem allocatedJointPlateau_residue_integral_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hactive : ∀ a, S.value ^ ((selected a).1.val + 1) < (axisK) a)
    (hgamma : ∀ a, (axisGamma) a ≤ S.value)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (M : A → ℕ) [∀ a, NeZero (M a)]
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (selected a) * (axisN) a)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (z : Y → ∀ a, (rows) a → ℤ)
    (w : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q) → Y → ℂ)
    (hz : Measurable z) (hw : ∀ r, Measurable (w r))
    (hweight : ∀ r, 0 < (tuples).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) →
      Integrable (fun y => if z y ∈ allocatedSelectedNaturalWindow (G := G) B U basis
        (R := R) rowFamily selected then ‖w r y‖ else 0) μ) :
    ‖(tuples).complexMean (fun v => ∫ y, w (principalResidueLabel q v) y *
        (((kernel v) (z y)).toReal : ℂ) ∂μ) -
      ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => ∫ y, w r y *
        allocatedJointPlateauProduct B U basis hR hσ S q rowFamily selected P δ
          hactive hq hsize M r (z y) ∂μ) / (volumeN : ℂ)‖ ≤
      (pointTolerance / volumeN) *
        ((tuples).fiberLaw (principalResidueLabel q)).mean (fun r => ∫ y,
          if z y ∈ allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected
          then ‖w r y‖ else 0 ∂μ) := by
  have hN : 0 < volumeN := by
    apply Finset.prod_pos
    intro a _
    exact pow_pos (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos B U basis hR S
      (selected a).1 (selected a).2 (hactive a))) _
  refine (tuples).conditional_window_weighted_integral_error
    (N := volumeN) (ε := pointTolerance) (principalResidueLabel q)
    kernel (allocatedSelectedNaturalWindow (G := G) B U basis (R := R) rowFamily selected)
    (allocatedJointPlateauProduct B U basis hR hσ S q rowFamily selected P δ hactive hq hsize M)
    μ z w hz hN hw ?_ ?_ hweight
  · intro r hr v hv
    exact allocatedJointWindow_data_support B U basis hR hσ S q rowFamily selected x P δ
      hselected hgrid hactive hq hsize M hrows r hr v hv
  · intro r hr v
    exact allocatedJointWindow_data_error B U basis hR hσ S q rowFamily selected x P δ
      hP hδ hselected hgrid hactive hgamma hq hsize L hL hcP hsP M hM hrows hB r hr v

end Erdos3.VectorPolynomial

end

end OAI
