/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))

noncomputable def allocatedGridAxisWindowVolume (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  (2 * allocatedNaturalSupportRadius (G := G) B α a.1 a.2 + 3) ^ (rowFamily a).card

theorem allocatedGridAxisWindowVolume_nonneg (a : Σ j : Fin m, Fin (n j)) :
    0 ≤ allocatedGridAxisWindowVolume (G := G) B rowFamily a := by
  have h := allocatedNaturalSupportRadius_nonneg (G := G) B α a.1 a.2
  unfold allocatedGridAxisWindowVolume
  positivity

noncomputable def allocatedGridFamilyWindowVolume : ℝ :=
  (1 + ∑ a, allocatedGridAxisWindowVolume (G := G) B rowFamily a) ^
    Fintype.card (Σ j : Fin m, Fin (n j))

theorem allocatedGridFamilyWindowVolume_nonneg :
    0 ≤ allocatedGridFamilyWindowVolume (G := G) B rowFamily := by
  have hs : 0 ≤ ∑ a, allocatedGridAxisWindowVolume (G := G) B rowFamily a :=
    Finset.sum_nonneg (fun a _ => allocatedGridAxisWindowVolume_nonneg (G := G) B rowFamily a)
  unfold allocatedGridFamilyWindowVolume
  positivity

theorem allocatedSelectedWindowVolume_le {A : Type*} [Fintype A]
    (selected : A → Σ j : Fin m, Fin (n j)) (hselected : Function.Injective selected) :
    (∏ a, allocatedGridAxisWindowVolume (G := G) B rowFamily (selected a)) ≤
      allocatedGridFamilyWindowVolume (G := G) B rowFamily := by
  let C := 1 + ∑ a, allocatedGridAxisWindowVolume (G := G) B rowFamily a
  have hs : 0 ≤ ∑ a, allocatedGridAxisWindowVolume (G := G) B rowFamily a :=
    Finset.sum_nonneg (fun a _ => allocatedGridAxisWindowVolume_nonneg (G := G) B rowFamily a)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hbound (a : A) : allocatedGridAxisWindowVolume (G := G) B rowFamily (selected a) ≤ C := by
    have h := Finset.single_le_sum
      (fun a _ => allocatedGridAxisWindowVolume_nonneg (G := G) B rowFamily a) (Finset.mem_univ (selected a))
    dsimp only [C]
    linarith
  calc
    _ ≤ ∏ _a : A, C := Finset.prod_le_prod₀
      (fun a _ => allocatedGridAxisWindowVolume_nonneg (G := G) B rowFamily (selected a)) (fun a _ => hbound a)
    _ = C ^ Fintype.card A := by simp only [Finset.prod_const, Finset.card_univ]
    _ ≤ C ^ Fintype.card (Σ j : Fin m, Fin (n j)) :=
      pow_le_pow_right₀ hC (Fintype.card_le_of_injective selected hselected)
    _ = allocatedGridFamilyWindowVolume (G := G) B rowFamily := rfl

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

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

def allocatedGridIntegerAxis : gridAxes → Σ j : Fin m, Fin (n j)
  | ⟨⟨_, Sum.inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, Sum.inr i⟩, _⟩ => ⟨j, i⟩

local notation "ig" => allocatedGridIntegerAxis B U b S

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridIntegerAxis_grid (a : gridAxes) :
    allocatedGridAxis (I := I) U b S.value ⟨(ig a).1, Sum.inr (ig a).2⟩ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ha

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridIntegerAxis_injective : Function.Injective ig := by
  have hinv (a : gridAxes) : (⟨(ig a).1, Sum.inr (ig a).2⟩ : LayerSamplerAxis I n) = a.val := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · rfl
  intro a c h
  apply Subtype.ext
  rw [← hinv a, ← hinv c, h]

def allocatedActiveGrid (a : gridAxes) : Prop :=
  S.value ^ ((ig a).1.val + 1) < basisAxisScale (b (ig a).1) (ig a).2

local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

def allocatedGridIntegerValues (a : gridAxes) (z : CoefficientJetAxisRow (rowTypes) a.val) :
    rowSets (ig a).1 → ℤ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact z

noncomputable def allocatedGridNaturalScale (a : gridAxes) : ℕ :=
  allocatedPrincipalGridScale (G := G) B U b (R := R) (ig a).1 (ig a).2

local notation "axisN" => allocatedGridNaturalScale B U b S

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridNaturalScale_pos (a : gridAxes) : 0 < axisN a :=
  allocatedPrincipalGridScale_pos_of_radius B U b hR (ig a).1 (ig a).2

noncomputable def allocatedGridNaturalWindow (a : gridAxes) :
    Finset (CoefficientJetAxisRow (rowTypes) a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact naturalScaleIntegerWindow (rowSets j) (allocatedNaturalSupportRadius (G := G) B α j i)
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedGridNaturalWindow_outside (a : gridAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val)
    (hz : z ∉ allocatedGridNaturalWindow B U b S rowSets a) :
    ¬∀ t, |(allocatedGridIntegerValues B U b S rowSets a z t : ℝ)| ≤
      allocatedNaturalSupportRadius (G := G) B α (ig a).1 (ig a).2 * axisN a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact fun h => hz (mem_naturalScaleIntegerWindow_of_bound _ _ _ h)

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedGridNaturalWindow_card_le (a : gridAxes) :
    ((allocatedGridNaturalWindow B U b S rowSets a).card : ℝ) ≤
      allocatedGridAxisWindowVolume (G := G) B (fun a => rowSets a.1) (ig a) *
        (axisN a : ℝ) ^ (rowSets (ig a).1).card := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · dsimp only [allocatedGridNaturalWindow, allocatedGridAxisWindowVolume,
      allocatedGridNaturalScale, allocatedGridIntegerAxis]
    convert naturalScaleIntegerWindow_card_le (rowSets j)
        (allocatedNaturalSupportRadius_nonneg (G := G) B α j i)
        (allocatedPrincipalGridScale_pos_of_radius (G := G) B U b hR j i) using 1
    · congr 2
    · simp only [Fintype.card_coe]

noncomputable def allocatedActiveNaturalVolume : ℝ :=
  ∏ a : activeAxes, (axisN a.val : ℝ) ^ (rowSets (ig a.val).1).card

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedActiveNaturalVolume_pos : 0 < allocatedActiveNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a.val)) _)

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedActiveWindow_volume :
    (∏ a : gridAxes, if allocatedActiveGrid B U b S a then
      ((allocatedGridNaturalWindow B U b S rowSets a).card : ℝ) else 1) ≤
      allocatedGridFamilyWindowVolume (G := G) B (fun a => rowSets a.1) *
        allocatedActiveNaturalVolume B U b S rowSets := by
  have heq := Fintype.prod_of_injective (fun a : activeAxes => a.val) Subtype.val_injective
    (fun a : activeAxes => ((allocatedGridNaturalWindow B U b S rowSets a.val).card : ℝ))
    (fun a : gridAxes => if allocatedActiveGrid B U b S a then
      ((allocatedGridNaturalWindow B U b S rowSets a).card : ℝ) else 1)
    (by
      intro a ha
      exact ite_eq_right (fun h => ha ⟨⟨a, h⟩, rfl⟩))
    (by intro a; rw [ite_eq_left a.property])
  rw [← heq]
  calc
    _ ≤ ∏ a : activeAxes, allocatedGridAxisWindowVolume (G := G) B (fun a => rowSets a.1) (ig a.val) *
        (axisN a.val : ℝ) ^ (rowSets (ig a.val).1).card :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun a _ => allocatedGridNaturalWindow_card_le B U b hR S rowSets a.val)
    _ = (∏ a : activeAxes, allocatedGridAxisWindowVolume (G := G) B (fun a => rowSets a.1) (ig a.val)) *
        allocatedActiveNaturalVolume B U b S rowSets := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (allocatedSelectedWindowVolume_le (G := G) B (fun a => rowSets a.1) (fun a : activeAxes => ig a.val)
        ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective))
      (allocatedActiveNaturalVolume_pos B U b hR S rowSets).le

variable (x : G → IntegerScalarCubeBox α S.value)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell

theorem allocatedSupportedGridJetPMF_integer (a : gridAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val) :
    (laws a z).toReal =
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell (ig a).1 (ig a).2
        (rowSets (ig a).1) x (allocatedGridIntegerValues B U b S rowSets a z)).toReal := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P ε : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

noncomputable def allocatedActivePlateauAxis (a : activeAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val.val) : ℂ :=
  allocatedBudgetedPlateauApproximation B U b hR hσ S q r (ig a.val).1 (ig a.val).2 a.property
    hq hsize P ε (M a) (rowSets (ig a.val).1) (allocatedGridIntegerValues B U b S rowSets a.val z)

theorem allocatedActivePlateauAxis_zero
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (a : activeAxes) (z : CoefficientJetAxisRow (rowTypes) a.val.val)
    (hz : z ∉ allocatedGridNaturalWindow B U b S rowSets a.val) :
    (laws a.val z).toReal = 0 ∧ allocatedActivePlateauAxis B U b hR hσ S rowSets q r hq hsize P ε M a z = 0 := by
  have hout := allocatedGridNaturalWindow_outside B U b S rowSets a.val z hz
  constructor
  · rw [allocatedSupportedGridJetPMF_integer B U b hR hσ S rowSets x q r hcell]
    rw [allocatedNaturalPhysicalPoint_zero_off_window B U b hR hσ S (ig a.val).1 (ig a.val).2
      a.property q r hq hsize hcell (allocatedGridIntegerAxis_grid B U b S a.val)
      (rowSets (ig a.val).1) (hrows _) x _ hout, ENNReal.toReal_zero]
  · exact allocatedBudgetedPlateau_zero_off_window B U b hR hσ S (ig a.val).1 (ig a.val).2
      a.property q r hq hsize P ε (M a) (rowSets (ig a.val).1) _ hout

theorem allocatedActivePlateauAxis_estimates
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
    (hε : 0 < ε) (hε1 : ε ≤ 1) (a : activeAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val.val) :
    ‖allocatedActivePlateauAxis B U b hR hσ S rowSets q r hq hsize P ε M a z‖ ≤
        allocatedGridPointCap B P (ig a.val) (rowSets (ig a.val).1) ∧
      ‖(((axisN a.val : ℝ) ^ (rowSets (ig a.val).1).card * (laws a.val z).toReal : ℝ) : ℂ) -
        allocatedActivePlateauAxis B U b hR hσ S rowSets q r hq hsize P ε M a z‖ ≤ ε := by
  constructor
  · exact allocatedBudgetedPlateauApproximation_norm_le B U b hR hσ S q r (ig a.val).1 (ig a.val).2
      a.property hq hsize (allocatedGridIntegerAxis_grid B U b S a.val) (hgamma a)
      L hL P hcP hsP (hM a) (rowSets (ig a.val).1) (hrows _) (hB a) ε _
  · rw [allocatedSupportedGridJetPMF_integer B U b hR hσ S rowSets x q r hcell]
    exact allocatedBudgetedPlateauApproximation_error B U b hR hσ S q r (ig a.val).1 (ig a.val).2
      a.property hq hsize hcell (allocatedGridIntegerAxis_grid B U b S a.val) (hgamma a)
      L hL P hcP hsP (hM a) (rowSets (ig a.val).1) (hrows _) (hB a) hε hε1 x _

end Erdos3.VectorPolynomial

end

end OAI
