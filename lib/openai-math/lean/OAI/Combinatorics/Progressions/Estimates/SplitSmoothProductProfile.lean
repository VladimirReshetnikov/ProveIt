/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.Progressions.Dynamics.ProductCutoffBudget
import OAI.Combinatorics.Progressions.Geometry.BoxChartCutoff
import OAI.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
import OAI.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
import OAI.Combinatorics.Progressions.Probability.SmoothProbabilityProfile

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def splitInputProfile (f : (J → ℝ) × (I → ℝ) → ℝ) (x : J ⊕ I → ℝ) : ℝ :=
  f ((fun j => x (.inl j)), (fun i => x (.inr i)))

theorem splitCoordinates_norm (x : J ⊕ I → ℝ) :
    ‖((fun j => x (.inl j)), (fun i => x (.inr i)))‖ = ‖x‖ := by
  apply le_antisymm
  · change max ‖fun j => x (.inl j)‖ ‖fun i => x (.inr i)‖ ≤ ‖x‖
    apply max_le
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun j => norm_le_pi_norm x (.inl j)
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => norm_le_pi_norm x (.inr i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    cases k with
    | inl j =>
      exact (norm_le_pi_norm (fun j => x (.inl j)) j).trans
        (norm_fst_le ((fun j => x (.inl j)), (fun i => x (.inr i))))
    | inr i =>
      exact (norm_le_pi_norm (fun i => x (.inr i)) i).trans
        (norm_snd_le ((fun j => x (.inl j)), (fun i => x (.inr i))))

theorem splitInputProfile_lipschitz {f : (J → ℝ) × (I → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (splitInputProfile f) := by
  have hs : LipschitzWith 1 (fun x : J ⊕ I → ℝ =>
      ((fun j => x (.inl j)), (fun i => x (.inr i)))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitCoordinates_norm (x - y)).le
  unfold splitInputProfile
  simpa only [mul_one, Function.comp_def] using hf.comp hs

theorem splitInputProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (x : J ⊕ I → ℝ) (hx : R < ‖x‖) :
    splitInputProfile f x = 0 :=
  hf _ (by rwa [splitCoordinates_norm])

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

omit [Fintype I] [Fintype J] in
theorem splitInputProfile_sample_sum (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ) :
    (∑' z : J ⊕ I → ℤ, splitInputProfile f (fun k => (z k : ℝ) / Sum.elim T S k)) =
      ∑' p : (I → ℤ) × (J → ℤ), scaledIntegerWeight f S T p := by
  let e : (J ⊕ I → ℤ) ≃ (I → ℤ) × (J → ℤ) :=
    (Equiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℤ)).trans (Equiv.prodComm _ _)
  exact e.tsum_eq (scaledIntegerWeight f S T)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def tensorCutoffWeight {ι : Type*} {E : ι → Type*} [Fintype ι] (w : ∀ i, E i → ℝ) (x : ∀ i, E i) : ℝ :=
  ∏ i, w i (x i)

theorem tensorCutoffWeight_nonneg {ι : Type*} {E : ι → Type*} [Fintype ι]
    (w : ∀ i, E i → ℝ) (hw : ∀ i x, 0 ≤ w i x) (x : ∀ i, E i) :
    0 ≤ tensorCutoffWeight w x := Finset.prod_nonneg (fun i _ => hw i (x i))

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

theorem tensorCutoffWeight_contDiff {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, ContDiff ℝ 1 (w i)) :
    ContDiff ℝ 1 (tensorCutoffWeight w) :=
  contDiff_prod (fun i _ => (hw i).comp
    (ContinuousLinearMap.proj i : (∀ j, E j) →L[ℝ] E i).contDiff)

theorem tensorCutoffWeight_integral {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ) :
    (∫ x, tensorCutoffWeight w x) = ∏ i, ∫ y, w i y :=
  integral_fintype_prod_volume_eq_prod w

theorem tensorCutoffWeight_abs_mass {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ) :
    (∫ x, |tensorCutoffWeight w x|) = ∏ i, ∫ y, |w i y| := by
  simp only [tensorCutoffWeight, Finset.abs_prod]
  exact integral_fintype_prod_volume_eq_prod (fun i y => |w i y|)

theorem tensorCutoffWeight_abs_mass_le_one {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ)
    (hw : ∀ i, (∫ y, |w i y|) ≤ 1) : (∫ x, |tensorCutoffWeight w x|) ≤ 1 := by
  rw [tensorCutoffWeight_abs_mass]
  exact Finset.prod_le_one₀ (fun i _ => integral_nonneg (fun y => abs_nonneg _)) (fun i _ => hw i)

theorem tensorCutoffWeight_mass_loss {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hm : ∀ i, (∫ y, w i y) ≤ 1)
    (e : ι → ℝ) (he : ∀ i, 1 - e i ≤ ∫ y, w i y) :
    1 - ∑ i, e i ≤ ∫ x, tensorCutoffWeight w x := by
  rw [tensorCutoffWeight_integral]
  have h := product_cutoff_loss_le (fun i => ∫ y, w i y)
    (fun i => ⟨integral_nonneg (hw i), hm i⟩)
  have hs : (∑ i, (1 - ∫ y, w i y)) ≤ ∑ i, e i :=
    Finset.sum_le_sum (fun i _ => by linarith [he i])
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scaledInputWeightSum (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) : ℝ := ∑' p : (I → ℤ) × (J → ℤ), scaledIntegerWeight f S T p

noncomputable def scaledInputMass (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) : ℝ := scaledInputWeightSum f S T / ((∏ i, S i) * (∏ j, T j))

theorem scaledIntegerWeight_summable (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) : Summable (scaledIntegerWeight f S T) := by
  let e : (J ⊕ I → ℤ) ≃ (I → ℤ) × (J → ℤ) :=
    (Equiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℤ)).trans (Equiv.prodComm _ _)
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  have h := scaledRectangularWeight_summable (splitInputProfile f) (fun _ => 0)
    (Sum.elim T S) (m := 1) zero_lt_one hscale (splitInputProfile_zero_outside hsupport)
  have heq (z : J ⊕ I → ℤ) : scaledIntegerWeight f S T (e z) =
      splitInputProfile f (fun k => (z k : ℝ) / Sum.elim T S k) := rfl
  have hs : Summable (fun z => scaledIntegerWeight f S T (e z)) := by
    simpa only [heq, zero_add, one_mul] using h
  exact e.summable_iff.mp hs

theorem scaledInputMass_error (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmeshS : ∀ i, 1 / S i ≤ δ) (hmeshT : ∀ j, 1 / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) :
    |scaledInputMass f S T - ∫ p, f p| ≤ (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K * δ := by
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  have hmesh : ∀ k, 1 / Sum.elim T S k ≤ δ := by
    intro k
    cases k with
    | inl j => exact hmeshT j
    | inr i => exact hmeshS i
  have h := rectangularLattice_quadrature (splitInputProfile f) (splitInputProfile_lipschitz hf)
    (fun _ => 0) (Sum.elim T S) hscale hR hδ hδ1 hmesh (splitInputProfile_zero_outside hsupport)
  unfold rectangularLatticePoint at h
  simp only [sub_zero, splitInputProfile_sample_sum, splitInputProfile_integral,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.card_sum] at h
  simpa only [scaledInputMass, scaledInputWeightSum, mul_comm (∏ j, T j) (∏ i, S i),
    add_comm (Fintype.card J) (Fintype.card I)] using h

theorem scaledInputMass_nonneg (f : (J → ℝ) × (I → ℝ) → ℝ) (hf : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 ≤ S i) (hT : ∀ j, 0 ≤ T j) :
    0 ≤ scaledInputMass f S T :=
  div_nonneg (tsum_nonneg (fun _ => hf _))
    (mul_nonneg (Finset.prod_nonneg fun i _ => hS i) (Finset.prod_nonneg fun j _ => hT j))

theorem scaledInputMass_bounds (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmeshS : ∀ i, 1 / S i ≤ δ) (hmeshT : ∀ j, 1 / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hmass : (∫ p, f p) = 1)
    (hsmall : (2 * R + 2) ^ (Fintype.card I + Fintype.card J) * K * δ ≤ 1 / 2) :
    1 / 2 ≤ scaledInputMass f S T ∧ scaledInputMass f S T ≤ 3 / 2 := by
  have h := scaledInputMass_error f hf S T hS hT hR hδ hδ1 hmeshS hmeshT hsupport
  rw [hmass, abs_le] at h
  constructor <;> linarith [h.1, h.2]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

noncomputable def sigmaAxisWeight (w : ∀ d, (I d → ℝ) → ℝ) (x : (Σ d, I d) → ℝ) : ℝ :=
  tensorCutoffWeight w (sigmaAxisCoordinates I x)

theorem sigmaAxisWeight_contDiff (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) : ContDiff ℝ 1 (sigmaAxisWeight w) :=
  (tensorCutoffWeight_contDiff w hw).comp (sigmaAxisCoordinates I).contDiff

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_compact (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, HasCompactSupport (w d)) : HasCompactSupport (sigmaAxisWeight w) :=
  (tensorCutoffWeight_compact w hw).comp_homeomorph (sigmaAxisCoordinates I).toHomeomorph

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_tsupport (w : ∀ d, (I d → ℝ) → ℝ)
    {x : (Σ d, I d) → ℝ} (hx : x ∈ tsupport (sigmaAxisWeight w)) (d : D) :
    sigmaAxisProjection I d x ∈ tsupport (w d) := by
  have he : tsupport (sigmaAxisWeight w) =
      (sigmaAxisCoordinates I) ⁻¹' tsupport (tensorCutoffWeight w) :=
    tsupport_comp_eq_preimage _ (sigmaAxisCoordinates I).toHomeomorph
  rw [he] at hx
  exact tensorCutoffWeight_tsupport w hx d

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

theorem sigmaAxisWeight_integral (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, sigmaAxisWeight w x) = ∏ d, ∫ y, w d y := by
  calc
    _ = ∫ x, tensorCutoffWeight w x :=
      (sigmaAxisCoordinates_measurePreserving I).integral_comp
        (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := tensorCutoffWeight_integral w

theorem sigmaAxisWeight_abs_mass (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, |sigmaAxisWeight w x|) = ∏ d, ∫ y, |w d y| := by
  have he (x : (Σ d, I d) → ℝ) : |sigmaAxisWeight w x| =
      sigmaAxisWeight (fun d y => |w d y|) x := by
    simp only [sigmaAxisWeight, tensorCutoffWeight, Finset.abs_prod]
  simp_rw [he]
  exact sigmaAxisWeight_integral _

theorem sigmaAxisWeight_abs_mass_le_one (w : ∀ d, (I d → ℝ) → ℝ)
    (hm : ∀ d, (∫ y, |w d y|) ≤ 1) : (∫ x, |sigmaAxisWeight w x|) ≤ 1 := by
  rw [sigmaAxisWeight_abs_mass]
  exact Finset.prod_le_one₀ (fun d _ => integral_nonneg (fun _ => abs_nonneg _)) (fun d _ => hm d)

theorem sigmaAxisWeight_mass_loss (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (hm : ∀ d, (∫ y, w d y) ≤ 1)
    (e : D → ℝ) (he : ∀ d, 1 - e d ≤ ∫ y, w d y) :
    1 - ∑ d, e d ≤ ∫ x, sigmaAxisWeight w x := by
  rw [sigmaAxisWeight_integral, ← tensorCutoffWeight_integral w]
  exact tensorCutoffWeight_mass_loss w hw hm e he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def smoothProductProfile (I : Type*) [Fintype I] (x : I → ℝ) : ℝ :=
  ∏ i, smoothProbabilityProfile (x i)

theorem smoothProductProfile_eq_cutoff (I : Type*) [Fintype I] :
    smoothProductProfile I = coordinateBoxCutoff smoothProbabilityProfile 1 := by
  funext x
  simp [smoothProductProfile, coordinateBoxCutoff]

theorem smoothProductProfile_contDiff (I : Type*) [Fintype I] :
    ContDiff ℝ ∞ (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact contDiff_coordinateBoxCutoff _ smoothProbabilityProfile_contDiff 1

theorem smoothProductProfile_compact (I : Type*) [Fintype I] :
    HasCompactSupport (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact hasCompactSupport_coordinateBoxCutoff _ smoothProbabilityProfile_zero zero_lt_one

theorem smoothProductProfile_range (I : Type*) [Fintype I] (x : I → ℝ) :
    0 ≤ smoothProductProfile I x ∧ smoothProductProfile I x ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (smoothProbabilityProfile_range (x i)).1),
    Finset.prod_le_one₀ (fun i _ => (smoothProbabilityProfile_range (x i)).1)
      (fun i _ => (smoothProbabilityProfile_range (x i)).2)⟩

theorem smoothProductProfile_norm_le (I : Type*) [Fintype I] (x : I → ℝ) :
    ‖smoothProductProfile I x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothProductProfile_range I x).1]
  exact (smoothProductProfile_range I x).2

theorem smoothProductProfile_zero_outside (I : Type*) [Fintype I]
    (x : I → ℝ) (hx : 1 < ‖x‖) : smoothProductProfile I x = 0 := by
  classical
  by_contra hn
  apply (not_le_of_gt hx)
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  by_contra! hi
  exact hn (Finset.prod_eq_zero (Finset.mem_univ i)
    (smoothProbabilityProfile_zero_outside (x i) hi))

theorem smoothProductProfile_integral (I : Type*) [Fintype I] :
    (∫ x, smoothProductProfile I x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun _ : I => smoothProbabilityProfile) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [smoothProbabilityProfile_integral, Finset.prod_const_one]

theorem smoothProductProfile_lipschitz (I : Type*) [Fintype I] :
    LipschitzWith (Fintype.card I * probabilityProfileLipschitz) (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  simpa only [div_one, NNReal.coe_one] using
    lipschitz_coordinateBoxCutoff smoothProbabilityProfile probabilityProfileLipschitz 1
      zero_lt_one smoothProbabilityProfile_range smoothProbabilityProfile_lipschitz

theorem smoothProductProfile_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (x : J → ℝ) : smoothProductProfile I (x ∘ e) = smoothProductProfile J x := by
  exact Equiv.prod_comp e (fun j => smoothProbabilityProfile (x j))

theorem smoothProductProfile_sum (I J : Type*) [Fintype I] [Fintype J]
    (x : I → ℝ) (y : J → ℝ) :
    smoothProductProfile (I ⊕ J) (Sum.elim x y) =
      smoothProductProfile I x * smoothProductProfile J y := by
  simp [smoothProductProfile, Fintype.prod_sum_type]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_update {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    (w : ∀ i, E i → ℝ) (i : ι) (g : E i → ℝ) (x : ∀ i, E i) :
    tensorCutoffWeight (Function.update w i g) x =
      g (x i) * ∏ j ∈ Finset.univ.erase i, w j (x j) := by
  unfold tensorCutoffWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem tensorCutoffWeight_fderiv_single {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ j, ContDiff ℝ 1 (w j)) (x : ∀ i, E i) (i : ι) (v : E i) :
    fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v) =
      (∏ j ∈ Finset.univ.erase i, w j (x j)) * fderiv ℝ (w i) (x i) v := by
  have hd (j : ι) : HasFDerivAt (fun y : ∀ i, E i => w j (y j))
      ((fderiv ℝ (w j) (x j)).comp (ContinuousLinearMap.proj j)) x :=
    ((hw j).differentiable one_ne_zero (x j)).hasFDerivAt.comp x (hasFDerivAt_apply j x)
  have h := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd j)
  change fderiv ℝ (fun y : ∀ i, E i => ∏ j, w j (y j)) x (Pi.single i v) = _
  rw [h.fderiv, sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, smul_eq_mul]
  · intro j _ hji
    simp [smul_apply, ContinuousLinearMap.comp_apply, hji]
  · simp

theorem tensorCutoffWeight_derivative_integral {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))]
    (w : ∀ i, E i → ℝ) (hw : ∀ j, ContDiff ℝ 1 (w j)) (i : ι) (v : E i) :
    (∫ x, |fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v)|) =
      (∫ y, |fderiv ℝ (w i) y v|) * ∏ j ∈ Finset.univ.erase i, ∫ y, |w j y| := by
  let a : ∀ i, E i → ℝ := fun j y => |w j y|
  let g : E i → ℝ := fun y => |fderiv ℝ (w i) y v|
  have he (x : ∀ i, E i) :
      |fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v)| =
        tensorCutoffWeight (Function.update a i g) x := by
    rw [tensorCutoffWeight_fderiv_single w hw, tensorCutoffWeight_update,
      abs_mul, Finset.abs_prod]
    exact mul_comm _ _
  simp_rw [he]
  rw [tensorCutoffWeight_integral, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem tensorCutoffWeight_derivative_le {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))]
    (w : ∀ i, E i → ℝ) (hw : ∀ j, ContDiff ℝ 1 (w j))
    (hm : ∀ j, (∫ y, |w j y|) ≤ 1) (i : ι) (v : E i) :
    (∫ x, |fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v)|) ≤
      ∫ y, |fderiv ℝ (w i) y v| := by
  rw [tensorCutoffWeight_derivative_integral w hw]
  exact mul_le_of_le_one_right (integral_nonneg (fun _ => abs_nonneg _))
    (Finset.prod_le_one₀ (fun j _ => integral_nonneg (fun y => abs_nonneg _)) (fun j _ => hm j))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def splitSmoothProductProfile (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  smoothProductProfile J p.1 * smoothProductProfile I p.2

theorem splitSmoothProductProfile_range (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    0 ≤ splitSmoothProductProfile J I p ∧ splitSmoothProductProfile J I p ≤ 1 := by
  have hJ := smoothProductProfile_range J p.1
  have hI := smoothProductProfile_range I p.2
  exact ⟨mul_nonneg hJ.1 hI.1, (mul_le_mul hJ.2 hI.2 hI.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem splitSmoothProductProfile_integrable (J I : Type*) [Fintype J] [Fintype I] :
    Integrable (splitSmoothProductProfile J I) :=
  binaryDensity_integrable
    ((smoothProductProfile_contDiff J).continuous.integrable_of_hasCompactSupport (smoothProductProfile_compact J))
    ((smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport (smoothProductProfile_compact I))

theorem splitSmoothProductProfile_integral (J I : Type*) [Fintype J] [Fintype I] :
    (∫ p, splitSmoothProductProfile J I p) = 1 := by
  change (∫ p, binaryDensity (smoothProductProfile J) (smoothProductProfile I) p ∂volume.prod volume) = 1
  rw [binaryDensity_mass, smoothProductProfile_integral, smoothProductProfile_integral, one_mul]

theorem splitSmoothProductProfile_lipschitz (J I : Type*) [Fintype J] [Fintype I] :
    LipschitzWith (((Fintype.card J + Fintype.card I : ℕ) : ℝ≥0) * probabilityProfileLipschitz)
      (splitSmoothProductProfile J I) := by
  have h := binaryDensity_lipschitz (smoothProductProfile J) (smoothProductProfile I) 1 1
    (Fintype.card J * probabilityProfileLipschitz) (Fintype.card I * probabilityProfileLipschitz)
    (smoothProductProfile_range J) (smoothProductProfile_range I)
    (smoothProductProfile_lipschitz J) (smoothProductProfile_lipschitz I)
  have he : binaryDensity (smoothProductProfile J) (smoothProductProfile I) =
      splitSmoothProductProfile J I := by funext p; rfl
  rw [← he]
  simpa only [one_mul, Nat.cast_add, add_mul] using h

theorem splitSmoothProductProfile_zero_outside (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) (hp : 1 < ‖p‖) : splitSmoothProductProfile J I p = 0 := by
  change 1 < max ‖p.1‖ ‖p.2‖ at hp
  rcases lt_max_iff.mp hp with h | h
  · exact mul_eq_zero_of_left (smoothProductProfile_zero_outside J p.1 h) _
  · exact mul_eq_zero_of_right _ (smoothProductProfile_zero_outside I p.2 h)

theorem splitSmoothProductProfile_join (J I : Type*) [Fintype J] [Fintype I] :
    splitInputProfile (splitSmoothProductProfile J I) = smoothProductProfile (J ⊕ I) := by
  funext x
  simp [splitInputProfile, splitSmoothProductProfile, smoothProductProfile, Fintype.prod_sum_type]

end Erdos3

end

end OAI
