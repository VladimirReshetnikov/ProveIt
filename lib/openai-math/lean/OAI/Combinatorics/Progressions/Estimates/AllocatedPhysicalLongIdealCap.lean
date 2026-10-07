/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.PhysicalIdealCapBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
import OAI.Combinatorics.Progressions.Estimates.SelectedProductEnvelope
import OAI.Combinatorics.Progressions.Geometry.FiniteRowChartRadiusBudget
import OAI.Combinatorics.Progressions.Geometry.NaturalWindowCoordinateBound
import OAI.Combinatorics.Progressions.Geometry.PhysicalActiveProfileRelativeSupport
import OAI.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedSiteCoefficientRadius (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  max (allocatedNaturalSupportRadius (G := G) B α a.1 a.2)
    ((2 : ℝ) ^ (a.1.val + 1) *
      (allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4))

theorem allocatedSiteCoefficientRadius_nonneg (a : Σ j : Fin m, Fin (n j)) :
    0 ≤ allocatedSiteCoefficientRadius (G := G) B rowSets a :=
  (allocatedNaturalSupportRadius_nonneg (G := G) B α a.1 a.2).trans (le_max_left _ _)

theorem allocatedSiteCoefficientRadius_physical (a : Σ j : Fin m, Fin (n j)) :
    allocatedNaturalSupportRadius (G := G) B α a.1 a.2 ≤
      allocatedSiteCoefficientRadius (G := G) B rowSets a := le_max_left _ _

theorem allocatedSiteCoefficientRadius_sites (a : Σ j : Fin m, Fin (n j)) :
    (2 : ℝ) ^ (a.1.val + 1) *
        (allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4) ≤
      allocatedSiteCoefficientRadius (G := G) B rowSets a := le_max_right _ _

noncomputable def allocatedSiteAxisWindowVolume (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  (2 * allocatedSiteCoefficientRadius (G := G) B rowSets a + 3) ^ (rowSets a.1).card

theorem allocatedSiteAxisWindowVolume_nonneg (a : Σ j : Fin m, Fin (n j)) :
    0 ≤ allocatedSiteAxisWindowVolume (G := G) B rowSets a := by
  have h := allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets a
  unfold allocatedSiteAxisWindowVolume
  positivity

noncomputable def allocatedSiteFamilyWindowVolume : ℝ :=
  (1 + ∑ a, allocatedSiteAxisWindowVolume (G := G) B rowSets a) ^
    Fintype.card (Σ j : Fin m, Fin (n j))

theorem allocatedSiteFamilyWindowVolume_nonneg :
    0 ≤ allocatedSiteFamilyWindowVolume (G := G) B rowSets := by
  have h : 0 ≤ ∑ a, allocatedSiteAxisWindowVolume (G := G) B rowSets a :=
    Finset.sum_nonneg (fun a _ => allocatedSiteAxisWindowVolume_nonneg (G := G) B rowSets a)
  unfold allocatedSiteFamilyWindowVolume
  positivity

noncomputable def allocatedSitePointTolerance (δ : ℝ) : ℝ :=
  δ / (allocatedSiteFamilyWindowVolume (G := G) B rowSets + 1)

theorem allocatedSitePointTolerance_spec {δ : ℝ} (hδ : 0 < δ) :
    0 < allocatedSitePointTolerance (G := G) B rowSets δ ∧
      allocatedSitePointTolerance (G := G) B rowSets δ *
        allocatedSiteFamilyWindowVolume (G := G) B rowSets ≤ δ := by
  have h := allocatedSiteFamilyWindowVolume_nonneg (G := G) B rowSets
  have hp : 0 < allocatedSiteFamilyWindowVolume (G := G) B rowSets + 1 := by linarith
  refine ⟨div_pos hδ hp, ?_⟩
  unfold allocatedSitePointTolerance
  calc
    _ ≤ (δ / (allocatedSiteFamilyWindowVolume (G := G) B rowSets + 1)) *
        (allocatedSiteFamilyWindowVolume (G := G) B rowSets + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hδ.le hp.le)
    _ = δ := div_mul_cancel₀ δ hp.ne'

variable [Fintype G] [∀ j, Fintype (I j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def allocatedGridSiteWindow (a : gridAxes) :
    Finset (CoefficientJetAxisRow (rowTypes) a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact naturalScaleIntegerWindow (rowSets j)
      (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩)
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)

theorem allocatedGridSiteWindow_mem (a : gridAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val)
    (hz : ∀ t, |(allocatedGridIntegerValues B U b S rowSets a z t : ℝ)| ≤
      allocatedSiteCoefficientRadius (G := G) B rowSets (ig a) * axisN a) :
    z ∈ allocatedGridSiteWindow B rowSets U b S a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact mem_naturalScaleIntegerWindow_of_bound _ _ _ hz

theorem allocatedGridSiteWindow_integer (a : gridAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val) :
    z ∈ allocatedGridSiteWindow B rowSets U b S a ↔
      allocatedGridIntegerValues B U b S rowSets a z ∈ naturalScaleIntegerWindow
        (rowSets (ig a).1) (allocatedSiteCoefficientRadius (G := G) B rowSets (ig a)) (axisN a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

theorem allocatedGridSiteWindow_card_le (hR : ∀ j, 0 < R j) (a : gridAxes) :
    ((allocatedGridSiteWindow B rowSets U b S a).card : ℝ) ≤
      allocatedSiteAxisWindowVolume (G := G) B rowSets (ig a) *
        (axisN a : ℝ) ^ (rowSets (ig a).1).card := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · dsimp only [allocatedGridSiteWindow, allocatedSiteAxisWindowVolume,
      allocatedGridNaturalScale, allocatedGridIntegerAxis]
    convert naturalScaleIntegerWindow_card_le (rowSets j)
      (allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩)
      (allocatedPrincipalGridScale_pos_of_radius (G := G) B U b hR j i) using 1
    · congr 2
    · simp only [Fintype.card_coe]

theorem allocatedActiveSiteWindow_volume (hR : ∀ j, 0 < R j) :
    (∏ a : gridAxes, if allocatedActiveGrid B U b S a then
      ((allocatedGridSiteWindow B rowSets U b S a).card : ℝ) else 1) ≤
      allocatedSiteFamilyWindowVolume (G := G) B rowSets *
        allocatedActiveNaturalVolume B U b S rowSets := by
  have heq := Fintype.prod_of_injective (fun a : activeAxes => a.val) Subtype.val_injective
    (fun a : activeAxes => ((allocatedGridSiteWindow B rowSets U b S a.val).card : ℝ))
    (fun a : gridAxes => if allocatedActiveGrid B U b S a then
      ((allocatedGridSiteWindow B rowSets U b S a).card : ℝ) else 1)
    (by intro a ha; exact ite_eq_right (fun h => ha ⟨⟨a, h⟩, rfl⟩))
    (by intro a; rw [ite_eq_left a.property])
  rw [← heq]
  calc
    _ ≤ ∏ a : activeAxes, allocatedSiteAxisWindowVolume (G := G) B rowSets (ig a.val) *
        (axisN a.val : ℝ) ^ (rowSets (ig a.val).1).card :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun a _ => allocatedGridSiteWindow_card_le B rowSets U b S hR a.val)
    _ = (∏ a : activeAxes, allocatedSiteAxisWindowVolume (G := G) B rowSets (ig a.val)) *
        allocatedActiveNaturalVolume B U b S rowSets := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (selected_nonnegative_product_le (allocatedSiteAxisWindowVolume (G := G) B rowSets)
        (allocatedSiteAxisWindowVolume_nonneg (G := G) B rowSets)
        (fun a : activeAxes => ig a.val)
        ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective))
      (allocatedActiveNaturalVolume_pos B U b hR S rowSets).le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedIdealCoverSupport (j : Fin m) : ℝ :=
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
    ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) +
  (partitionedIdealRadius α m + 1) +
  ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1)

theorem allocatedIdealCoverSupport_nonneg (j : Fin m) :
    0 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hi := partitionedIdealRadius_nonneg α m
  have hw : 0 ≤ ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) :=
    Finset.sum_nonneg (fun i _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩])
  unfold allocatedIdealCoverSupport
  positivity

theorem allocatedIdealCoverSupport_inactive (j : Fin m) :
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤
        allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hi := partitionedIdealRadius_nonneg α m
  have hw : 0 ≤ ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) :=
    Finset.sum_nonneg (fun i _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩])
  unfold allocatedIdealCoverSupport
  linarith

theorem allocatedIdealCoverSupport_ideal (j : Fin m) :
    partitionedIdealRadius α m + 1 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hw : 0 ≤ ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) :=
    Finset.sum_nonneg (fun i _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩])
  unfold allocatedIdealCoverSupport
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (by positivity)) hw

theorem allocatedIdealCoverSupport_window (j : Fin m) (i : Fin (n j)) :
    allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
      allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hi := partitionedIdealRadius_nonneg α m
  have hw := Finset.single_le_sum (s := Finset.univ)
    (f := fun k : Fin (n j) => allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, k⟩ + 1)
    (fun k _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, k⟩])
    (Finset.mem_univ i)
  apply hw.trans
  unfold allocatedIdealCoverSupport
  exact le_add_of_nonneg_left (by positivity)

noncomputable def allocatedIdealCoverRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  finiteRowChartRadius (rowSets j).card (Fintype.card (I j)) (C j)
    (allocatedIdealCoverSupport (G := G) B rowSets j)

theorem allocatedIdealCoverRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedIdealCoverRadius (G := G) B rowSets C j :=
  finiteRowChartRadius_pos _ _ (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

include hR in
theorem allocatedActiveWindow_scaled_bound (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (b j) i)
    (z : rowSets j → ℤ)
    (hz : z ∈ naturalScaleIntegerWindow (rowSets j)
      (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩)
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)) (t : rowSets j) :
    |(z t : ℝ) / basisAxisScale (b j) i| ≤
      (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) * R j := by
  have hN := allocatedPrincipalGridScale_pos B U b hR S j i hactive
  have hH := allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩
  have hzt := naturalScaleIntegerWindow_coordinate_bound hH hN hz t
  have hscale := (allocatedPrincipalGridScale_bounds B U b hR S j i hactive).2
  have hl : (0 : ℝ) < basisAxisScale (b j) i := Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
  have hγ : 2 * principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) ≤ R j := by
    unfold principalProfileSize
    have hd : (0 : ℝ) < 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith [hR j, Nat.cast_nonneg (α := ℝ) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))]
  rw [abs_div, abs_of_pos hl]
  apply (div_le_iff₀ hl).mpr
  calc
    _ ≤ (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) *
        (2 * principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) *
          basisAxisScale (b j) i) := hzt.trans (mul_le_mul_of_nonneg_left hscale (by linarith))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hγ hl.le]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "rowTypes" => (fun j => {t : Finset α // t ∈ rowSets j})
local notation "output" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

noncomputable def allocatedPhysicalLongIdeal (δ : ℝ≥0) : (output → ℝ) → ℝ :=
  physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) grid
    (fun a => (Subtype.val : rowTypes a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ

theorem allocatedPhysicalLongIdeal_measurable (δ : ℝ≥0) :
    Measurable (allocatedPhysicalLongIdeal B U b hR S rowSets δ) :=
  physicalActiveProfileIdeal_measurable (G × Option α) (layerSamplerDegree I n) grid
    (fun a => (Subtype.val : rowTypes a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ

theorem allocatedPhysicalLongIdeal_relative_support (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : output → ℝ) (hv : allocatedPhysicalLongIdeal B U b hR S rowSets δ v ≠ 0)
    (a : {a // ¬grid a}) (t : rowTypes a.val.1) :
    |v ⟨a, t⟩| ≤ (partitionedIdealRadius α m + 1) * R a.val.1 :=
  physicalActiveProfileIdeal_relative_support (G × Option α) (layerSamplerDegree I n) grid
    (fun a => (Subtype.val : rowTypes a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) (fun a => Nat.succ_le_of_lt a.1.isLt)
    δ hδ hδ1 v hv ⟨a, t⟩

theorem allocatedPhysicalLongIdeal_cover_support (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : output → ℝ) (hv : allocatedPhysicalLongIdeal B U b hR S rowSets δ v ≠ 0)
    (a : {a // ¬grid a}) (t : rowTypes a.val.1) :
    |v ⟨a, t⟩| ≤ allocatedIdealCoverSupport (G := G) B rowSets a.val.1 * R a.val.1 :=
  (allocatedPhysicalLongIdeal_relative_support B U b hR S rowSets δ hδ hδ1 v hv a t).trans
    (mul_le_mul_of_nonneg_right (allocatedIdealCoverSupport_ideal B rowSets a.val.1)
      (hR a.val.1).le)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

noncomputable def allocatedIdealProfileLog {A : Type*} [Semiring A] (m : ℕ) (p e : A) : A :=
  allocatedComparisonDimension m p * (p + e)

theorem allocatedIdealProfileLog_nonneg (m : ℕ) {p e : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) :
    0 ≤ allocatedIdealProfileLog m p e :=
  mul_nonneg (allocatedComparisonDimension_bounds m hp).1 (add_nonneg hp he)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "rowTypes" => (fun j => {t : Finset α // t ∈ rowSets j})
local notation "output" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

theorem allocatedPhysicalLongIdeal_exp_bound {D p e : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e)
    (hcard : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ D)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (v : output → ℝ) :
    |allocatedPhysicalLongIdeal B U b hR S rowSets δ v| ≤ Real.exp (D * (p + e)) := by
  have hc : Fintype.card output ≤ Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) := by
    apply Fintype.card_le_of_injective (fun q : output => ⟨q.1.val, q.2⟩)
    rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
    cases h
    rfl
  exact physicalActiveProfileIdeal_exp_bound (G × Option α) (layerSamplerDegree I n) grid
    (fun a => (Subtype.val : rowTypes a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) hp he ((Nat.cast_le.mpr hc).trans hcard)
    (fun a => hRi a.1) δ hδ hδe v

theorem allocatedPhysicalLongIdeal_primitive_bound {p e : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e)
    (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (v : output → ℝ) :
    |allocatedPhysicalLongIdeal B U b hR S rowSets δ v| ≤ Real.exp (allocatedIdealProfileLog m p e) := by
  have hd := allocatedComparisonDimensions_of_primitive B
    (fun j => (Subtype.val : rowTypes j → Finset α)) hdim
    (fun _ => Subtype.val_injective) hp hvars hI hn
  exact allocatedPhysicalLongIdeal_exp_bound B U b hR S rowSets hp he hd.outputs hRi δ hδ hδe v

end Erdos3.VectorPolynomial

end

end OAI
