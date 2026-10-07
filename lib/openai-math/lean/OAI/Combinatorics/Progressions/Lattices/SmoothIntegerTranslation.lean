import OAI.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
import OAI.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def smoothAffineSample {K I : Type*} [Fintype K] (t : K → ℤ)
    (z : Option K × I → ℤ) : I → ℤ :=
  fun i => z (none, i) + ∑ k, t k * z (some k, i)

theorem smoothAffineSample_base_injective {K I : Type*} [Fintype K]
    (t : K → ℤ) (tail : K × I → ℤ) :
    Function.Injective (fun base => smoothAffineSample t (baseArrayJoin tail base)) := by
  intro b c h
  funext i
  have hi := congrFun h i
  change b i + (∑ k, t k * tail (k, i)) = c i + (∑ k, t k * tail (k, i)) at hi
  exact add_right_cancel hi

theorem smoothAffineSample_point_cap {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (y : I → ℤ) :
    ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffineSample t) y).toReal ≤
      ∏ i, 2 / S (none, i) :=
  shiftedSmoothProductPMF_base_cap a S hS hZ (smoothAffineSample t)
    (smoothAffineSample_base_injective t) hbase y

theorem smoothAffineSample_energy {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0) :
    (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * e (smoothAffineSample t z) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * ∑ y ∈ T, e y ^ 2 :=
  pmf_image_energy_of_point_cap (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (smoothAffineSample t) T e he (smoothAffineSample_point_cap a S hS hZ hbase t)

theorem smoothAffineSample_energy_of_sum_bound {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (hbase : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S (none, i))
    (t : K → ℤ) (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E : ℝ} (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card) :
    (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * e (smoothAffineSample t z) ^ 2) ≤
      (∏ i, 2 / S (none, i)) * (E * T.card) := by
  exact (smoothAffineSample_energy a S hS hZ hbase t T e he).trans
    (mul_le_mul_of_nonneg_left henergy (Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothAffineSample_variation {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z w : Option J × I → ℤ) (i : I)
    {T V r0 rV rt : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (ht : ∀ j, |(t j : ℝ)| ≤ T)
    (hw : ∀ j, |(w (some j, i) : ℝ)| ≤ V)
    (hbase : |(z (none, i) : ℝ) - w (none, i)| ≤ r0)
    (hdir : ∀ j, |(z (some j, i) : ℝ) - w (some j, i)| ≤ rV)
    (hparam : ∀ j, |(t j : ℝ) - u j| ≤ rt) :
    |(smoothAffineSample t z i : ℝ) - smoothAffineSample u w i| ≤
      r0 + (Fintype.card J : ℝ) * (T * rV + V * rt) := by
  have hid : (smoothAffineSample t z i : ℝ) - smoothAffineSample u w i =
      ((z (none, i) : ℝ) - w (none, i)) +
        ∑ j, ((t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i)) := by
    simp only [smoothAffineSample, Int.cast_add, Int.cast_sum, Int.cast_mul, Finset.sum_sub_distrib]
    ring
  have hterm (j : J) : |(t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i)| ≤ T * rV + V * rt := by
    calc
      _ = |(t j : ℝ) * ((z (some j, i) : ℝ) - w (some j, i)) +
          (w (some j, i) : ℝ) * ((t j : ℝ) - u j)| := by congr 1; ring
      _ ≤ |(t j : ℝ) * ((z (some j, i) : ℝ) - w (some j, i))| +
          |(w (some j, i) : ℝ) * ((t j : ℝ) - u j)| := abs_add_le _ _
      _ ≤ T * rV + V * rt := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (ht j) (hdir j) (abs_nonneg _) hT)
          (mul_le_mul (hw j) (hparam j) (abs_nonneg _) hV)
  rw [hid]
  calc
    _ ≤ |(z (none, i) : ℝ) - w (none, i)| +
        |∑ j, ((t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i))| := abs_add_le _ _
    _ ≤ r0 + ∑ j, |(t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i)| :=
      add_le_add hbase (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ r0 + ∑ _j : J, (T * rV + V * rt) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hterm j))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem smoothAffineSample_scaled_variation {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z w : Option J × I → ℤ) (i : I)
    {L H C B delta : ℝ} (hL : 0 < L) (hH : 0 ≤ H) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (ht : ∀ j, |(t j : ℝ)| ≤ C * L)
    (hw : ∀ j, |(w (some j, i) : ℝ)| ≤ B * H / L)
    (hbase : |(z (none, i) : ℝ) - w (none, i)| ≤ delta * H)
    (hdir : ∀ j, |(z (some j, i) : ℝ) - w (some j, i)| ≤ delta * H / L)
    (hparam : ∀ j, |(t j : ℝ) - u j| ≤ delta * L) :
    |(smoothAffineSample t z i : ℝ) - smoothAffineSample u w i| ≤
      delta * H * (1 + (Fintype.card J : ℝ) * (C + B)) := by
  apply (smoothAffineSample_variation t u z w i (by positivity) (by positivity) ht hw hbase hdir hparam).trans_eq
  field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem shiftedSmoothRowMass_pos {J I : Type*} [Fintype J] [Fintype I]
    (a S : J × I → ℝ) (hS : ∀ x, 0 < S x) (hZ : 0 < shiftedSmoothProductMass a S) (i : I) :
    0 < shiftedSmoothProductMass (fun j => a (j, i)) (fun j => S (j, i)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun j => hS (j, i))]
  exact Finset.prod_pos (fun j _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (j, i))

theorem shiftedSmoothProductPMF_rows {J I : Type*} [Fintype J] [Fintype I]
    (a S : J × I → ℝ) (hS : ∀ x, 0 < S x) (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map independentArrayRows =
      independentProductPMF (fun i => shiftedSmoothProductPMF
        (fun j => a (j, i)) (fun j => S (j, i)) (fun j => hS (j, i))
        (shiftedSmoothRowMass_pos a S hS hZ i)) := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_rows]
  congr 1
  funext i
  exact (shiftedSmoothProductPMF_eq_independent _ _ _ _).symm

def smoothAffinePairRows {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z : Option K × I → ℤ) : I → Fin 2 → ℤ :=
  fun i => affinePairMatrix t u *ᵥ independentArrayRows z i

theorem smoothAffinePairRows_apply {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z : Option K × I → ℤ) (i : I) :
    smoothAffinePairRows t u z i = ![smoothAffineSample t z i, smoothAffineSample u z i] := by
  rw [smoothAffinePairRows, affinePairMatrix_mulVec]
  rfl

theorem shiftedSmoothAffinePairRows_law {K I : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ x, 0 < S x) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : K → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u) =
      independentProductPMF (fun i =>
        (shiftedSmoothProductPMF (fun j => a (j, i)) (fun j => S (j, i))
          (fun j => hS (j, i)) (shiftedSmoothRowMass_pos a S hS hZ i)).map
            (fun z => affinePairMatrix t u *ᵥ z)) := by
  have h := congrArg (fun p : PMF (I → Option K → ℤ) =>
    p.map (fun rows i => affinePairMatrix t u *ᵥ rows i))
      (shiftedSmoothProductPMF_rows a S hS hZ)
  rw [PMF.map_comp, independentProductPMF_map] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem smoothAffinePairRows_congruence {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z : Option J × I → ℤ) (i : I) :
    BohrLattice.Primitive.content (fun j => u j - t j) ∣
      smoothAffinePairRows t u z i 1 - smoothAffinePairRows t u z i 0 := by
  apply (affinePairImage_iff_content_dvd t u _).mp
  exact ⟨independentArrayRows z i, rfl⟩

theorem affinePairPMF_zero_off_congruence {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (v : I → Fin 2 → ℤ)
    (hv : ¬ ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ v i 1 - v i 0) :
    p.map (smoothAffinePairRows t u) v = 0 := by
  apply pmf_map_zero_off_range
  rintro ⟨z, rfl⟩
  exact hv (smoothAffinePairRows_congruence t u z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem shiftedSmoothSampleSum_integer (b : ℤ) (S : ℝ) :
    shiftedSmoothSampleSum (b : ℝ) S = smoothSampleSum S := by
  have h := (Equiv.addRight b).tsum_eq
    (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - b) / S))
  simpa only [Equiv.coe_addRight, Int.cast_add, add_sub_cancel_right,
    shiftedSmoothSampleSum, smoothSampleSum] using h.symm

theorem shiftedSmoothProductMass_integer_pos {I : Type*} [Fintype I]
    (b : I → ℤ) (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S := by
  rw [shiftedSmoothProductMass_eq_prod _ _ hS]
  simp_rw [shiftedSmoothSampleSum_integer]
  exact Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i))

theorem shiftedSmoothCoefficientPMF_integer (b : ℤ) (S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum (b : ℝ) S) :
    shiftedSmoothCoefficientPMF (b : ℝ) S hS hZ =
      (smoothCoefficientPMF S hS).map (fun z => z + b) := by
  ext z
  have hmap := pmf_map_injective_at (smoothCoefficientPMF S hS) (fun z => z + b)
    (fun _ _ h => add_right_cancel h) (z - b)
  rw [sub_add_cancel] at hmap
  rw [hmap]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [shiftedSmoothCoefficientPMF_apply, smoothCoefficientPMF_apply, shiftedSmoothSampleSum_integer]
  simp only [Int.cast_sub]

theorem shiftedSmoothProductPMF_integer {I : Type*} [Fintype I]
    (b : I → ℤ) (S : I → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S) :
    shiftedSmoothProductPMF (fun i => (b i : ℝ)) S hS hZ =
      (smoothProductPMF S hS).map (fun z => z + b) := by
  change _ = (smoothProductPMF S hS).map (fun z i => z i + b i)
  rw [shiftedSmoothProductPMF_eq_independent, smoothProductPMF_eq_independent,
    independentProductPMF_map (fun i => smoothCoefficientPMF (S i) (hS i)) (fun i z => z + b i)]
  congr 1
  funext i
  exact shiftedSmoothCoefficientPMF_integer (b i) (S i) (hS i) _

theorem smoothAffinePairRows_add {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z b : Option K × I → ℤ) :
    smoothAffinePairRows t u (z + b) = smoothAffinePairRows t u z + smoothAffinePairRows t u b := by
  funext i
  change affinePairMatrix t u *ᵥ (independentArrayRows z i + independentArrayRows b i) = _
  exact Matrix.mulVec_add _ _ _

theorem shiftedSmoothAffinePairRows_integer {K I : Type*} [Fintype K] [Fintype I]
    (b : Option K × I → ℤ) (S : Option K × I → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S) (t u : K → ℤ) :
    (shiftedSmoothProductPMF (fun i => (b i : ℝ)) S hS hZ).map (smoothAffinePairRows t u) =
      ((smoothProductPMF S hS).map (smoothAffinePairRows t u)).map
        (fun v => v + smoothAffinePairRows t u b) := by
  rw [shiftedSmoothProductPMF_integer, PMF.map_comp, PMF.map_comp]
  congr 1
  funext z
  exact smoothAffinePairRows_add t u z b

theorem shiftedSmoothAffinePairRows_integer_apply {K I : Type*} [Fintype K] [Fintype I]
    (b : Option K × I → ℤ) (S : Option K × I → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass (fun i => (b i : ℝ)) S) (t u : K → ℤ)
    (v : I → Fin 2 → ℤ) :
    ((shiftedSmoothProductPMF (fun i => (b i : ℝ)) S hS hZ).map (smoothAffinePairRows t u)) v =
      ((smoothProductPMF S hS).map (smoothAffinePairRows t u)) (v - smoothAffinePairRows t u b) := by
  rw [shiftedSmoothAffinePairRows_integer]
  have h := pmf_map_injective_at ((smoothProductPMF S hS).map (smoothAffinePairRows t u))
    (fun v => v + smoothAffinePairRows t u b) (fun _ _ h => add_right_cancel h)
    (v - smoothAffinePairRows t u b)
  simpa only [sub_add_cancel] using h

end Erdos3

end

end OAI
