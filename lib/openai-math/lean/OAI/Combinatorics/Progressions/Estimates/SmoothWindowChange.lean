import OAI.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem exists_bounded_change_of_measure {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) {C : ℝ} (hC : 0 < C)
    (hdom : ∀ x, q.weight x ≤ C * p.weight x) :
    ∃ w : Ω → ℝ, (∀ x, 0 ≤ w x ∧ w x ≤ 1) ∧
      ∀ f : Ω → ℝ, q.mean f = C * p.mean (fun x => w x * f x) := by
  let w : Ω → ℝ := fun x => q.weight x / (C * p.weight x)
  have hw (x : Ω) : 0 ≤ w x ∧ w x ≤ 1 := by
    refine ⟨div_nonneg (q.nonneg x) (mul_nonneg hC.le (p.nonneg x)), ?_⟩
    by_cases hp : p.weight x = 0
    · simp [w, hp]
    · exact (div_le_one (mul_pos hC (lt_of_le_of_ne (p.nonneg x) (Ne.symm hp)))).mpr
        (hdom x)
  refine ⟨w, hw, fun f => ?_⟩
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : p.weight x = 0
  · have hq : q.weight x = 0 := le_antisymm (by simpa [hp] using hdom x) (q.nonneg x)
    simp [hp, hq]
  · dsimp only [w]
    field_simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_window_change_of_measure {X : Type*} [DecidableEq X]
    (S W : Finset X) (hWS : W ⊆ S) (p : FiniteProbabilityWeights S)
    {D : ℝ} (hD : 0 < D)
    (hlower : ∀ z : S, z.val ∈ W → 1 ≤ D * p.weight z) :
    ∃ w : S → ℝ, (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : X → ℝ, (𝔼 z ∈ W, f z) =
        (D / W.card) * p.mean (fun z => w z * f z.val) := by
  let w : S → ℝ := fun z => if z.val ∈ W then 1 / (D * p.weight z) else 0
  have hw (z : S) : 0 ≤ w z ∧ w z ≤ 1 := by
    dsimp only [w]
    split_ifs with hz
    · have hpos : 0 < D * p.weight z := lt_of_lt_of_le zero_lt_one (hlower z hz)
      exact ⟨div_nonneg zero_le_one hpos.le, (div_le_one hpos).mpr (hlower z hz)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  refine ⟨w, hw, fun f => ?_⟩
  have hpoint (z : S) : D * (p.weight z * (w z * f z.val)) =
      if z.val ∈ W then f z.val else 0 := by
    by_cases hz : z.val ∈ W
    · have hp : p.weight z ≠ 0 := by
        intro h
        have hh := hlower z hz
        norm_num [h] at hh
      simp only [w, hz, ite_true]
      field_simp
    · simp [w, hz]
  have hsum : D * p.mean (fun z => w z * f z.val) = ∑ z ∈ W, f z := by
    unfold FiniteProbabilityWeights.mean
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_coe_sort S (fun z => if z ∈ W then f z else 0)]
    calc
      _ = ∑ z ∈ W, if z ∈ W then f z else 0 :=
        (Finset.sum_subset hWS (fun z _ hz => by simp [hz])).symm
      _ = _ := Finset.sum_congr rfl (fun z hz => by simp [hz])
  rw [Finset.expect_eq_sum_div_card, ← hsum]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def smoothSourceFiniteWeights {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (rectangularWeightIndices a S 1) where
  weight z := (shiftedSmoothProductPMF a S hS hZ z.val).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
      (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal)]
    have h : (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal) =
        ∑ z ∈ rectangularWeightIndices a S 1, (shiftedSmoothProductPMF a S hS hZ z).toReal :=
      (hasSum_sum_of_ne_finset_zero (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)).tsum_eq
    rw [← h]
    exact shiftedSmoothProductPMF_toReal_sum a S hS hZ

theorem smoothSourceFiniteWeights_mean {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (J → ℤ) → ℝ) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => f z.val) =
      ∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * f z := by
  unfold FiniteProbabilityWeights.mean
  change (∑ z : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ z.val).toReal * f z.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal * f z)]
  exact (hasSum_sum_of_ne_finset_zero (fun z hz => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hz, zero_mul])).tsum_eq.symm

theorem smoothSourceFiniteWeights_energy {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E : ℝ} (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => e (smoothAffineSample t z.val) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * (E * T.card) := by
  rw [smoothSourceFiniteWeights_mean a S hS hZ (fun z => e (smoothAffineSample t z) ^ 2)]
  exact smoothAffineSample_energy_of_sum_bound a S hS hZ hbase t T e he henergy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smooth_inner_mem_indices {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    z ∈ rectangularWeightIndices a S 1 := by
  classical
  by_contra hn
  have h := shiftedSmoothProductPMF_inner_mass a S hS hZ hscale z hz
  rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hn, mul_zero] at h
  norm_num at h

theorem smooth_window_change_of_measure {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (I → ℤ)) (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    ∃ w : rectangularWeightIndices a S 1 → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      ∀ f : (I → ℤ) → ℝ, (𝔼 z ∈ W, f z) =
        ((3 : ℝ) ^ Fintype.card I * (∏ i, S i) / W.card) *
          (smoothSourceFiniteWeights a S hS hZ).mean (fun z => w z * f z.val) := by
  classical
  have hsub : W ⊆ rectangularWeightIndices a S 1 :=
    fun z hz => smooth_inner_mem_indices a S hS hZ hscale z (hW z hz)
  have hD : 0 < ∏ i, 3 * S i :=
    Finset.prod_pos (fun i _ => mul_pos (by norm_num) (hS i))
  have h := finite_window_change_of_measure (rectangularWeightIndices a S 1) W hsub
    (smoothSourceFiniteWeights a S hS hZ) hD
    (fun z hz => shiftedSmoothProductPMF_inner_mass a S hS hZ hscale z.val (hW z.val hz))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

theorem shiftedSmoothProductMass_pos_of_large_scales {I : Type*} [Fintype I]
    (a S : I → ℝ) (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hscale i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hscale i))

end Erdos3

end

end OAI
