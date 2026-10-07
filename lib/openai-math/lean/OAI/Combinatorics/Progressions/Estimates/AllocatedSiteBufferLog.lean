/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
import OAI.Combinatorics.Progressions.Geometry.AllocatedPhysicalLongBoxVolume

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

theorem allocatedIdealSiteCutoff_mul (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ idealSiteBoxRadius α m) → χ v = 1)
    (z : AllocatedLongJetRows B U b S jets) :
    (∏ s : Finset α, χ (allocatedIdealSiteCoordinates B U b S z s)) *
      physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) =
      physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) := by
  by_cases hz : physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
      (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) = 0
  · rw [hz, mul_zero]
  · have hprod : (∏ s : Finset α, χ (allocatedIdealSiteCoordinates B U b S z s)) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      apply hone
      intro a
      exact allocatedIdealSiteCoordinates_bound_of_ne_zero B U b S hR δ hδ hδ1 z hz s a
    rw [hprod, one_mul]

theorem allocatedIdealSiteCutoff_complex_mul (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ idealSiteBoxRadius α m) → χ v = 1)
    (z : AllocatedLongJetRows B U b S jets) :
    (∏ s : Finset α, (χ (allocatedIdealSiteCoordinates B U b S z s) : ℂ)) *
      (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) =
      (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
  exact_mod_cast allocatedIdealSiteCutoff_mul B U b S hR δ hδ hδ1 χ hone z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

noncomputable def allocatedIdealSiteEnvelope (z : AllocatedLongJetRows B U b S jets) : ℝ :=
  if ∀ s a, |allocatedIdealSiteCoordinates B U b S z s a| ≤ 2 * idealSiteBoxRadius α m then
    (∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1)⁻¹
  else 0

theorem allocatedIdealSiteEnvelope_nonneg (hR : ∀ j, 0 < R j)
    (z : AllocatedLongJetRows B U b S jets) : 0 ≤ allocatedIdealSiteEnvelope B U b S z := by
  unfold allocatedIdealSiteEnvelope
  split_ifs
  · exact inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
  · exact le_rfl

theorem allocatedIdealNormalizedJets_bound_of_sites
    (z : AllocatedLongJetRows B U b S jets) {C : ℝ} (hC : 0 ≤ C)
    (hsites : ∀ s a, |allocatedIdealSiteCoordinates B U b S z s a| ≤ C) :
    ‖fun q : (Σ a : {a // ¬grid a}, jets a.val.1) =>
        allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1‖ ≤ (2 : ℝ)^Fintype.card α * C := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro q
  rw [Real.norm_eq_abs]
  have h := booleanCoefficient_abs_le (fun s => allocatedIdealSiteCoordinates B U b S z s q.1.val)
    q.2.val (fun s _ => hsites s q.1.val)
  rw [allocatedIdealSiteCoordinates_jet] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.card_le_univ q.2.val)) hC)

theorem allocatedIdealSiteApproximation_envelope {T : Type*} [Fintype T]
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (c : T → ℂ) (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) (ε : ℝ)
    (hsupport : ∀ i s v, (∃ a, 2 * idealSiteBoxRadius α m < |v a|) → f i s v = 0)
    (he : ∀ z : AllocatedLongJetRows B U b S jets,
      ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α))
          (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) /
          ((∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1 : ℝ) : ℂ)‖ ≤
        ε / (∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1))
    (z : AllocatedLongJetRows B U b S jets) :
    ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) /
        ((∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1 : ℝ) : ℂ)‖ ≤
      ε * allocatedIdealSiteEnvelope B U b S z := by
  by_cases hb : ∀ s a, |allocatedIdealSiteCoordinates B U b S z s a| ≤ 2 * idealSiteBoxRadius α m
  · simpa only [allocatedIdealSiteEnvelope, ite_eq_left hb, div_eq_mul_inv] using he z
  · obtain ⟨s, a, ha⟩ : ∃ s a, 2 * idealSiteBoxRadius α m < |allocatedIdealSiteCoordinates B U b S z s a| := by
      simpa only [not_forall, not_le] using hb
    have hlarge : idealSiteBoxRadius α m < |allocatedIdealSiteCoordinates B U b S z s a| := by
      have hr := idealSiteBoxRadius_pos α m
      linarith
    have hi := allocatedIdealSiteCoordinates_zero_outside B U b S hR δ hδ hδ1 z s a hlarge
    have hsum : (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hprod : (∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ s) (hsupport i s _ ⟨a, ha⟩)
      rw [hprod, mul_zero]
    rw [hi, Complex.ofReal_zero, hsum, zero_div, sub_self, norm_zero,
      allocatedIdealSiteEnvelope, ite_eq_right hb, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

theorem allocatedIdealSiteApproximation_error {T : Type*} [Fintype T]
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ idealSiteBoxRadius α m) → χ v = 1)
    (a : T → ℂ) (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) (ε : ℝ)
    (herr : ∀ v : Finset α → LayerSamplerAxis I n → ℝ,
      ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ
          (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
            (fun s d => v s d.val)) : ℂ) - ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε)
    (z : AllocatedLongJetRows B U b S jets) :
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ‖(volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      ∑ i, a i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)‖ ≤ ε ∧
    ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      (∑ i, a i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro volume
  have hdensity := congrArg Complex.ofReal (allocatedIdealSiteCoordinates_density B U b S hR δ z)
  simp only [Complex.ofReal_mul] at hdensity
  have hcutoff := allocatedIdealSiteCutoff_complex_mul B U b S hR δ hδ hδ1 χ hone z
  have hpoint := herr (allocatedIdealSiteCoordinates B U b S z)
  rw [← hdensity] at hpoint
  have hproduct : (∏ s : Finset α, (χ (allocatedIdealSiteCoordinates B U b S z s) : ℂ)) *
      ((volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α)) (fun a => R a.1) (fun a => hR a.1) δ
        (allocatedLongJetRealCoordinates B U b S z) : ℂ)) =
      (volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α)) (fun a => R a.1) (fun a => hR a.1) δ
        (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
    rw [mul_left_comm, hcutoff]
  rw [hproduct] at hpoint
  refine ⟨hpoint, ?_⟩
  have hvolume : 0 < volume := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hvolumeC : (volume : ℂ) ≠ 0 := by exact_mod_cast hvolume.ne'
  calc
    _ = ‖((volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α)) (fun a => R a.1) (fun a => hR a.1) δ
          (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        ∑ i, a i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / (volume : ℂ)‖ := by
      congr 1
      field_simp [hvolumeC]
    _ = _ := by rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvolume]
    _ ≤ _ := div_le_div_of_nonneg_right hpoint hvolume.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

theorem allocatedIdealSiteCoordinates_measurable :
    Measurable (allocatedIdealSiteCoordinates (α := α) B U b S) := by
  unfold allocatedIdealSiteCoordinates
  apply (realSitesFromBoundedJets_lipschitz (α := α)
    (fun a : LayerSamplerAxis I n => (a.1 : ℕ) + 1)).continuous.measurable.comp
  apply Measurable.of_eval
  intro q
  by_cases ha : ¬grid q.1
  · simpa only [dite_eq_left ha, Function.comp_def] using
      ((measurable_pi_apply ⟨⟨q.1, ha⟩, q.2⟩).comp
        (allocatedLongJetRealCoordinates_measurable B U b S (O := jets))).div_const (R q.1.1)
  · simpa only [dite_eq_right ha] using
      (measurable_const : Measurable (fun _ : AllocatedLongJetRows B U b S jets => (0 : ℝ)))

theorem allocatedIdealSiteSupport_measurable :
    MeasurableSet {z : AllocatedLongJetRows B U b S jets |
      ∀ s a, |allocatedIdealSiteCoordinates B U b S z s a| ≤ 2 * idealSiteBoxRadius α m} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro s
  apply MeasurableSet.iInter
  intro a
  exact measurableSet_le
    (((measurable_pi_apply a).comp ((measurable_pi_apply s).comp
      (allocatedIdealSiteCoordinates_measurable B U b S))).abs) measurable_const

theorem allocatedIdealSiteEnvelope_measurable :
    Measurable (allocatedIdealSiteEnvelope (α := α) B U b S) := by
  unfold allocatedIdealSiteEnvelope
  exact Measurable.ite (allocatedIdealSiteSupport_measurable B U b S) measurable_const measurable_const

theorem allocatedIdealSiteEnvelope_le_box (hR : ∀ j, 0 < R j)
    (z : AllocatedLongJetRows B U b S jets) :
    allocatedIdealSiteEnvelope B U b S z ≤
      (allocatedPhysicalLongJetBox B U b S jets
        ((2 : ℝ) ^ Fintype.card α * (2 * idealSiteBoxRadius α m))).indicator
          (fun _ => (∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1)⁻¹) z := by
  have hr : 0 ≤ 2 * idealSiteBoxRadius α m := (mul_pos (by norm_num) (idealSiteBoxRadius_pos α m)).le
  have hv : 0 ≤ (∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1)⁻¹ :=
    inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
  by_cases hs : ∀ s a, |allocatedIdealSiteCoordinates B U b S z s a| ≤ 2 * idealSiteBoxRadius α m
  · have hz := allocatedPhysicalLongJetBox_of_normalizedCoordinates B U b S jets hR
      (mul_nonneg (by positivity) hr) z
      (allocatedIdealNormalizedJets_bound_of_sites B U b S z hr hs)
    simp only [allocatedIdealSiteEnvelope, ite_eq_left hs, Set.indicator_of_mem hz, le_refl]
  · simp only [allocatedIdealSiteEnvelope, ite_eq_right hs]
    exact Set.indicator_nonneg (fun _ _ => hv) z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_ideal_site_approximation (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : ((m : ℝ) + 2) * Fintype.card α + 3 ≤ p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let radius : ℝ≥0 := ⟨idealSiteBoxRadius α m, (idealSiteBoxRadius_pos α m).le⟩
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * idealSiteBoxRadius α m < |v d|) → f i s v = 0) ∧
        ∀ z : AllocatedLongJetRows B U b S jets,
          ‖(volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
              (fun a => (Subtype.val : jets a.val.1 → Finset α))
              (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            ∑ i, a i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)‖ ≤ ε ∧
          ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
              (fun a => (Subtype.val : jets a.val.1 → Finset α))
              (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            (∑ i, a i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro radius C Q volume
  have hbound : 2 * (radius : ℝ) ≤ Real.exp p :=
    (idealSiteBoxRadius_buffer_le_exp α m).trans (Real.exp_le_exp.mpr hbox)
  obtain ⟨χ, hone, k, hk, hcard, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_normalized_active_ideal_site_approximation (G := G) (Z := G × Option α) (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1)
      hLayer grid (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ hδ
      radius (idealSiteBoxRadius_pos α m) hε hp hbound hεp hδp
  let alternateUniverse : Finset (Finset α × LayerSamplerAxis I n → Fin k) :=
    @Finset.univ _ (@Pi.instFintype (Finset α × LayerSamplerAxis I n) (fun _ => Fin k)
      (@instDecidableEqProd (Finset α) (LayerSamplerAxis I n) inferInstance
        (fun a b => Classical.propDecidable (a = b)))
      inferInstance (fun _ => Fin.fintype k))
  have huniv : (Finset.univ : Finset (Finset α × LayerSamplerAxis I n → Fin k)) =
      alternateUniverse := by
    ext i
    simp only [alternateUniverse, Finset.mem_univ]
  have hcard' : (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) := by
    simpa only [Q, Fintype.card_eq_nat_card] using hcard
  refine ⟨k, hk, hcard', a, f, ?_, hf, ?_, hfsupport, ?_⟩
  · calc
      (∑ i, ‖a i‖) = alternateUniverse.sum (fun i => ‖a i‖) := by rw [huniv]
      _ ≤ _ := ha
  · simpa only [Q] using hLf
  · intro z
    refine allocatedIdealSiteApproximation_error B U b S hR δ hδ hδ1 χ hone a f ε ?_ z
    intro v
    rw [huniv]
    exact herr v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹
local notation "radius" => idealSiteEnvelopeRadius α m

noncomputable def allocatedSiteBuffer (v : output → ℝ) : ℝ :=
  invVolume * idealSiteBuffer α m output (fun q => v q / R q.1.val.1)

noncomputable def allocatedSiteBufferLip (M : ℝ≥0) : ℝ≥0 :=
  ‖invVolume‖₊ * ((Fintype.card output * normalizedSiteCutoffBound /
    (2 * ⟨radius, (idealSiteEnvelopeRadius_pos α m).le⟩)) * M)

theorem allocatedSiteBuffer_range (hR : ∀ j, 0 < R j) (v : output → ℝ) :
    0 ≤ allocatedSiteBuffer B U b S v ∧ allocatedSiteBuffer B U b S v ≤ invVolume := by
  have hJ : 0 ≤ invVolume := inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
  have hχ := (idealSiteBuffer_spec α m output).2.2.1 (fun q => v q / R q.1.val.1)
  exact ⟨mul_nonneg hJ hχ.1, mul_le_of_le_one_right hJ hχ.2⟩

theorem allocatedSiteBuffer_abs_le (hR : ∀ j, 0 < R j) (v : output → ℝ) :
    |allocatedSiteBuffer B U b S v| ≤ ‖invVolume‖₊ := by
  have hJ : 0 ≤ invVolume := inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
  simpa only [abs_of_nonneg (allocatedSiteBuffer_range B U b S hR v).1,
    coe_nnnorm, Real.norm_of_nonneg hJ] using (allocatedSiteBuffer_range B U b S hR v).2

theorem allocatedSiteBuffer_measurable :
    Measurable (allocatedSiteBuffer (α := α) B U b S) := by
  have hs : Measurable (fun v : output → ℝ => fun q => v q / R q.1.val.1) :=
    Measurable.of_eval (fun coordinate => (measurable_pi_apply coordinate).div_const _)
  exact measurable_const.mul (((idealSiteBuffer_spec α m output).1.continuous.measurable).comp hs)

theorem allocatedSiteBuffer_lipschitz (hR : ∀ j, 0 < R j) (M : ℝ≥0)
    (hInv : ∀ j, (R j)⁻¹ ≤ M) :
    LipschitzWith (allocatedSiteBufferLip (α := α) B U b S M) (allocatedSiteBuffer (α := α) B U b S) := by
  have hs : LipschitzWith M (fun v : output → ℝ => fun q => v q / R q.1.val.1) := by
    have hc := coordinateScale_lipschitz (fun q : output => (R q.1.val.1)⁻¹)
      (fun q => (abs_of_pos (inv_pos.mpr (hR q.1.val.1))).le.trans (hInv q.1.val.1))
    simpa only [div_eq_mul_inv, mul_comm] using hc
  have hi := ((idealSiteBuffer_spec α m output).2.2.2.2.2).comp hs
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [Real.dist_eq, allocatedSiteBuffer, ← mul_sub, abs_mul]
  simpa only [allocatedSiteBufferLip, Function.comp_def, Real.dist_eq, NNReal.coe_mul,
    coe_nnnorm, Real.norm_eq_abs, mul_assoc] using
    mul_le_mul_of_nonneg_left (hi.dist_le_mul v w) (abs_nonneg invVolume)

theorem allocatedSiteBuffer_support (v : output → ℝ) (hv : allocatedSiteBuffer B U b S v ≠ 0) :
    ‖fun q : output => v q / R q.1.val.1‖ ≤ 2 * radius := by
  have hχ : idealSiteBuffer α m output (fun q => v q / R q.1.val.1) ≠ 0 :=
    (mul_ne_zero_iff.mp hv).2
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (idealSiteEnvelopeRadius_pos α m).le)).mpr
  intro q
  simpa only [Real.norm_eq_abs] using (idealSiteBuffer_spec α m output).2.2.2.2.1 _ hχ q

variable [DecidableEq α]

theorem allocatedIdealSiteEnvelope_le_buffer (hR : ∀ j, 0 < R j)
    (z : AllocatedLongJetRows B U b S jets) :
    allocatedIdealSiteEnvelope B U b S z ≤
      allocatedSiteBuffer B U b S (allocatedLongJetRealCoordinates B U b S z) := by
  by_cases hs : ∀ s a, |allocatedIdealSiteCoordinates B U b S z s a| ≤ 2 * idealSiteBoxRadius α m
  · have hnorm := allocatedIdealNormalizedJets_bound_of_sites B U b S z
      (mul_nonneg (by norm_num) (idealSiteBoxRadius_pos α m).le) hs
    have hχ : idealSiteBuffer α m output
        (fun q => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1) = 1 := by
      apply (idealSiteBuffer_spec α m output).2.2.2.1
      intro q
      simpa only [Real.norm_eq_abs, idealSiteEnvelopeRadius] using
        (norm_le_pi_norm (fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1) q).trans hnorm
    simp only [allocatedIdealSiteEnvelope, ite_eq_left hs, allocatedSiteBuffer, hχ, mul_one, le_refl]
  · rw [allocatedIdealSiteEnvelope, ite_eq_right hs]
    exact (allocatedSiteBuffer_range B U b S hR _).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹

theorem allocatedSiteBuffer_cap_le_exp {D p : ℝ} (hp : 0 ≤ p)
    (hcard : (Fintype.card output : ℝ) ≤ D)
    (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) :
    (‖invVolume‖₊ : ℝ) ≤ Real.exp (D * p) :=
  (inverseProduct_norm_le_exp (fun q : output => R q.1.val.1)
    (fun q => hR q.1.val.1) (fun q => hRi q.1.val.1)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hp))

theorem allocatedSiteBuffer_lip_le_exp {D p : ℝ} (hp : 0 ≤ p)
    (hcard : (Fintype.card output : ℝ) ≤ D)
    (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) :
    (allocatedSiteBufferLip (α := α) B U b S ⟨Real.exp p, (Real.exp_pos p).le⟩ : ℝ) ≤
      Real.exp (D * p + D + (normalizedSiteCutoffBound : ℝ) + p) := by
  have hc := allocatedSiteBuffer_cap_le_exp (α := α) B U b S hp hcard hR hRi
  let radiusNN : ℝ≥0 := ⟨idealSiteEnvelopeRadius α m, (idealSiteEnvelopeRadius_pos α m).le⟩
  let cut : ℝ≥0 := Fintype.card output * normalizedSiteCutoffBound / (2 * radiusNN)
  have hl : (cut : ℝ) ≤ Real.exp (D + (normalizedSiteCutoffBound : ℝ)) :=
    idealSiteBuffer_lip_le_exp α m output hcard
  change (‖invVolume‖₊ : ℝ) * ((cut : ℝ) * Real.exp p) ≤ _
  calc
    _ ≤ Real.exp (D * p) * (Real.exp (D + (normalizedSiteCutoffBound : ℝ)) * Real.exp p) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
