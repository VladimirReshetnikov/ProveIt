/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

 theorem coordinateAffine_norm_le_one {I : Type*} [Fintype I]
    (center width : I → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (x : I → ℝ) (hx : ‖x‖ ≤ 1) : ‖fun i => center i + width i * x i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hi : |x i| ≤ 1 := (norm_le_pi_norm x i).trans hx
  calc
    ‖center i + width i * x i‖ ≤ |center i| + |width i| * |x i| := by
      simpa only [Real.norm_eq_abs, abs_mul] using norm_add_le (center i) (width i * x i)
    _ ≤ |center i| + |width i| := add_le_add le_rfl
      (by simpa using mul_le_mul_of_nonneg_left hi (abs_nonneg (width i)))
    _ ≤ 1 := hw i

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

 theorem partitionedSlicedRegularizedIdeal_zero_outside {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : partitionedIdealRadius α degree + 1 < ‖v‖) :
    partitionedSlicedRegularizedIdeal h P sets ρ center width z v = 0 := by
  apply regularizedImageDensity_support
    (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (fun x => partitionedIdealMap h P sets z (fun i => center i + width i * x i))
    ρ hρ (partitionedIdealRadius_nonneg α degree)
  · filter_upwards [jointBooleanSource_ae_closedBall
      (α := α) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)] with x hx
    apply partitionedIdealMap_norm_le h P sets hdegree z hz
    apply coordinateAffine_norm_le_one center width hw x
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · have hd : (ρ : ℝ) ≤ 1 := hρ1
    linarith

 theorem activeAveragedSlicedProfileIdeal_zero_outside {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : partitionedIdealRadius α degree + 1 < ‖v‖) :
    activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P)] with r hr
  exact partitionedSlicedRegularizedIdeal_zero_outside Z h P sets hdegree ρ hρ hρ1 center width hw
    (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)
    (profileNoiseWithActive_abs_le h P (fun _ => 0) r (fun _ => by simp) hr) v hv

 theorem activeScaledSlicedIdeal_bounds (R : (Σ d, O d) → ℝ) {C : ℝ≥0}
    (hR : ∀ i, |(R i)⁻¹| ≤ C) (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (∀ v, |diagonalImageDensity R
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width) v| ≤
        (∏ i, |R i|)⁻¹ * (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (‖(∏ i, |R i|)⁻¹‖₊ * (affineProductProfileLip (Σ d, O d) ρ * C))
      (diagonalImageDensity R (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width)) := by
  have hs := activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) Z h P sets ρ hρ center width
  refine ⟨diagonalImageDensity_bound R _ (fun v => ?_),
    diagonalImageDensity_lipschitz R _ hs.2.1 hR⟩
  rw [abs_of_nonneg (hs.1 v).1]
  exact (hs.1 v).2

 theorem activeScaledSlicedIdeal_zero_outside (R : (Σ d, O d) → ℝ)
    (hR : ∀ i, R i ≠ 0) {C : ℝ} (hC : 0 ≤ C) (hRC : ∀ i, |R i| ≤ C)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : C * (partitionedIdealRadius α degree + 1) < ‖v‖) :
    diagonalImageDensity R (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width) v = 0 :=
  diagonalImageDensity_zero_outside R hR _ hC hRC
    (activeAveragedSlicedProfileIdeal_zero_outside (G := G) (B := B) Z h P sets
      hdegree ρ hρ hρ1 center width hw) v hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def realRowsSiteValue (rows : Finset (Finset α))
    (v : rows → ℝ) (s : Finset α) : ℝ :=
  ∑ t : rows, v t * (if t.val ⊆ s then 1 else 0)

omit [Fintype α] in
theorem realRowsSiteValue_coefficient (rows : Finset (Finset α))
    (v : rows → ℝ) (s : rows) :
    booleanCoefficient (realRowsSiteValue rows v) s.val = v s := by
  unfold realRowsSiteValue
  rw [booleanCoefficient_sum]
  simp only [booleanCoefficient_const_mul, booleanCoefficient_monomial]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    have hst : s.val ≠ t.val := fun he => hts (Subtype.ext he.symm)
    simp only [hst, ite_false, mul_zero]
  · simp

omit [Fintype α] in
theorem realRowsSiteValue_bound (rows : Finset (Finset α))
    (v : rows → ℝ) {T : ℝ} (hT : 0 ≤ T) (hv : ∀ t, |v t| ≤ T) (s : Finset α) :
    |realRowsSiteValue rows v s| ≤ rows.card * T := by
  simpa only [realRowsSiteValue, rowRestrictedSiteMatrix, booleanReconstructionMatrix, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_comm]
    using rowRestrictedSiteMatrix_real_bound rows v hT hv s

namespace VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets

noncomputable def allocatedRowIdealCoordinates (z : AllocatedLongJetRows B U b S rowTypes) :
    Finset α → LayerSamplerAxis I n → ℝ :=
  fun s a => realRowsSiteValue (rowSets a.1) (fun t =>
    if ha : ¬grid a then allocatedLongJetRealCoordinates B U b S z ⟨⟨a, ha⟩, t⟩ / R a.1
    else 0) s

omit [Fintype α] in
theorem allocatedRowIdealCoordinates_jet (z : AllocatedLongJetRows B U b S rowTypes)
    (a : {a // ¬grid a}) (t : rowTypes a.val.1) :
    booleanCoefficient (fun s => allocatedRowIdealCoordinates B U b S rowSets z s a.val) t.val =
      allocatedLongJetRealCoordinates B U b S z ⟨a, t⟩ / R a.val.1 := by
  unfold allocatedRowIdealCoordinates
  rw [realRowsSiteValue_coefficient]
  simp only [dite_eq_left a.property]

omit [Fintype α] in
theorem allocatedRowIdealCoordinates_physical_jets (hR : ∀ j, 0 < R j)
    (z : AllocatedLongJetRows B U b S rowTypes) :
    booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : rowTypes a.val.1 → Finset α))
      (fun s a => R a.val.1 * allocatedRowIdealCoordinates B U b S rowSets z s a.val) =
      allocatedLongJetRealCoordinates B U b S z := by
  funext q
  change booleanCoefficient
    (fun s => R q.1.val.1 * allocatedRowIdealCoordinates B U b S rowSets z s q.1.val) q.2.val = _
  rw [booleanCoefficient_const_mul, allocatedRowIdealCoordinates_jet]
  field_simp [(hR q.1.val.1).ne']

theorem allocatedRowIdealCoordinates_density (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (z : AllocatedLongJetRows B U b S rowTypes) :
    (∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1) *
        allocatedPhysicalLongIdeal B U b hR S rowSets δ (allocatedLongJetRealCoordinates B U b S z) =
      activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) grid
        (fun a => (Subtype.val : rowTypes a.val.1 → Finset α)) δ
        (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : rowTypes a.val.1 → Finset α))
          (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val)) := by
  have h := physicalActiveProfileIdeal_normalized_sites (G := G) (Z := G × Option α) (B := B)
    (O := fun a : LayerSamplerAxis I n => rowTypes a.1)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : rowTypes a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ (allocatedRowIdealCoordinates B U b S rowSets z)
  rw [allocatedRowIdealCoordinates_physical_jets B U b S rowSets hR z] at h
  exact h

theorem allocatedRowIdealCoordinates_bound (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (z : AllocatedLongJetRows B U b S rowTypes)
    (hz : allocatedPhysicalLongIdeal B U b hR S rowSets δ (allocatedLongJetRealCoordinates B U b S z) ≠ 0)
    (s : Finset α) (a : LayerSamplerAxis I n) :
    |allocatedRowIdealCoordinates B U b S rowSets z s a| ≤ (radius : ℝ) := by
  unfold allocatedRowIdealCoordinates
  apply (realRowsSiteValue_bound (rowSets a.1) _ (allocatedIdealCoverSupport_nonneg B rowSets a.1) ?_ s).trans
    (allocatedProductIdealSiteRadius_dominates B rowSets a.1)
  intro t
  by_cases ha : ¬grid a
  · rw [dite_eq_left ha, abs_div, abs_of_pos (hR a.1)]
    exact (div_le_iff₀ (hR a.1)).mpr
      (allocatedPhysicalLongIdeal_cover_support B U b hR S rowSets δ hδ hδ1 _ hz ⟨a, ha⟩ t)
  · rw [dite_eq_right ha, abs_zero]
    exact allocatedIdealCoverSupport_nonneg B rowSets a.1

omit [Fintype α] in
theorem allocatedRowIdealCoordinates_mixed_value
    {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ)
    (z : MixedCoveredJetSource I rowTypes E n d) (s : Finset α) :
    allocatedRowIdealCoordinates B U b S rowSets ((coefficientJetAxisSplit rowTypes I n grid z.1).2) s =
      allocatedNormalizedMixedSiteValue B U b S
        (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) := by
  funext a
  rcases a with ⟨j, i | i⟩
  · change realRowsSiteValue (rowSets j)
      (fun t => if _h : ¬grid ⟨j, Sum.inl i⟩ then (z.1 j).1 i t / R j else 0) s =
      (if grid ⟨j, Sum.inl i⟩ then 0 else
        (∑ t : rowTypes j, (rowRestrictedSiteMatrix (rowSets j) s t : ℝ) * (z.1 j).1 i t) / R j)
    by_cases hg : grid ⟨j, Sum.inl i⟩
    · simp only [hg, not_true_eq_false, dite_false, ite_true, realRowsSiteValue, zero_mul, Finset.sum_const_zero]
    · simp only [hg, not_false_eq_true, dite_true, ite_false, realRowsSiteValue,
        rowRestrictedSiteMatrix, booleanReconstructionMatrix, Int.cast_ite, Int.cast_one, Int.cast_zero,
        Finset.sum_div, mul_comm]
      apply Finset.sum_congr rfl
      intro t _
      ring
  · change realRowsSiteValue (rowSets j)
      (fun t => if _h : ¬grid ⟨j, Sum.inr i⟩ then
        ((z.1 j).2 i t : ℝ) / (basisAxisScale (b j) i : ℝ) / R j else 0) s =
      (if grid ⟨j, Sum.inr i⟩ then 0 else
        ((∑ t : rowTypes j, rowRestrictedSiteMatrix (rowSets j) s t * (z.1 j).2 i t : ℤ) : ℝ) /
          (basisAxisScale (b j) i : ℝ) / R j)
    by_cases hg : grid ⟨j, Sum.inr i⟩
    · simp only [hg, not_true_eq_false, dite_false, ite_true, realRowsSiteValue, zero_mul, Finset.sum_const_zero]
    · simp only [hg, not_false_eq_true, dite_true, ite_false, realRowsSiteValue, Int.cast_sum, Int.cast_mul,
        rowRestrictedSiteMatrix, booleanReconstructionMatrix, Int.cast_ite, Int.cast_one, Int.cast_zero,
        Finset.sum_div, mul_comm]
      apply Finset.sum_congr rfl
      intro t _
      ring

end VectorPolynomial
end Erdos3

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
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

noncomputable def allocatedRowSlicedIdeal (ρ : ℝ≥0) (center width : input → ℝ) :
    (output → ℝ) → ℝ :=
  diagonalImageDensity (fun o : output => R o.1.val.1)
    (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α)) ρ center width)

noncomputable def allocatedRowSlicedSiteRadius : ℝ≥0 :=
  ⟨1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1), by
    have := partitionedIdealRadius_nonneg α m
    positivity⟩

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_one_le : 1 ≤ allocatedRowSlicedSiteRadius rowSets := by
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1)
  have ht := partitionedIdealRadius_nonneg α m
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => by positivity))

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_pos : 0 < allocatedRowSlicedSiteRadius rowSets := by
  change (0 : ℝ) < 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1)
  have := partitionedIdealRadius_nonneg α m
  positivity

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_dominates (j : Fin m) :
    (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ allocatedRowSlicedSiteRadius rowSets := by
  change _ ≤ 1 + ∑ k : Fin m, (rowSets k).card * (partitionedIdealRadius α m + 1)
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  exact (Finset.single_le_sum (f := fun k : Fin m =>
    (rowSets k).card * (partitionedIdealRadius α m + 1))
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) hT) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem allocatedRowSlicedIdealCoordinates_density (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (center width : input → ℝ) (z : AllocatedLongJetRows B U b S jets) :
    (∏ q : output, R q.1.val.1) *
        allocatedRowSlicedIdeal B U b S rowSets ρ center width (allocatedLongJetRealCoordinates B U b S z) =
      activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α)) ρ center width
        (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
          (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val)) := by
  have hjet : booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
      (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val) =
      (fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1) := by
    funext q
    exact allocatedRowIdealCoordinates_jet B U b S rowSets z q.1 q.2
  rw [hjet]
  unfold allocatedRowSlicedIdeal diagonalImageDensity
  simp only [abs_of_pos (hR _)]
  rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun q _ => (hR q.1.val.1).ne')), one_mul]

theorem allocatedRowSlicedIdealCoordinates_bound
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (z : AllocatedLongJetRows B U b S jets)
    (hz : allocatedRowSlicedIdeal B U b S rowSets ρ center width
      (allocatedLongJetRealCoordinates B U b S z) ≠ 0)
    (s : Finset α) (a : LayerSamplerAxis I n) :
    |allocatedRowIdealCoordinates B U b S rowSets z s a| ≤
      (allocatedRowSlicedSiteRadius rowSets : ℝ) := by
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hv : ‖fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1‖ ≤
      partitionedIdealRadius α m + 1 := by
    by_contra hn
    apply hz
    unfold allocatedRowSlicedIdeal diagonalImageDensity
    rw [activeAveragedSlicedProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => Nat.succ_le_of_lt a.1.isLt) ρ hρ hρ1 center width hw _ (lt_of_not_ge hn), mul_zero]
  unfold allocatedRowIdealCoordinates
  apply (realRowsSiteValue_bound (rowSets a.1) _ hT ?_ s).trans
    (allocatedRowSlicedSiteRadius_dominates rowSets a.1)
  intro t
  by_cases ha : ¬grid a
  · rw [dite_eq_left ha]
    exact (norm_le_pi_norm (fun q : output =>
      allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1) ⟨⟨a, ha⟩, t⟩).trans hv
  · rw [dite_eq_right ha, abs_zero]
    exact hT

end Erdos3.VectorPolynomial

end

end OAI
