import GRHArticle.ProgressionFree.IntegerReciprocalDensity
import GRHArticle.ProgressionFree.IntegerSmoothFactorization

/-!
# The smooth optimization bounds natural density from above

A rough part indexes a fiber of admissible smooth multipliers. Each fiber
has total reciprocal weight at most the fixed-set smooth optimum.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators Classical

private def smoothFiber (A : Set ℕ) (Y r : ℕ) : Set ℕ :=
  {s | s ∈ Nat.smoothNumbers (Y+1) ∧ r*s ∈ A}

private theorem smoothFiber_admissible {A : Set ℕ} {integral : Bool} {Y r : ℕ}
    (hA : IntegerPrefixAdmissible integral A) (hr : 0 < r) :
    IntegerPrefixAdmissible integral (smoothFiber A Y r) := by
  intro a b c ha hb hc hab hbc he hd
  apply hA ha.2 hb.2 hc.2 (Nat.mul_lt_mul_of_pos_left hab hr) (Nat.mul_lt_mul_of_pos_left hbc hr)
  · calc
      (r*a)*(r*c) = (r*r)*(a*c) := by ring
      _ = (r*r)*(b*b) := by rw [he]
      _ = (r*b)*(r*b) := by ring
  · exact fun h ↦ Nat.mul_dvd_mul_left r (hd h)

private theorem smoothSubset_reciprocal_summable {Y : ℕ} {D : Set ℕ}
    (hD : D ⊆ Nat.smoothNumbers (Y+1)) : Summable (fun s : D ↦ (s.val:ℝ)⁻¹) := by
  let emb : D → Nat.smoothNumbers (Y+1) := fun x ↦ ⟨x.val,hD x.property⟩
  have he : Function.Injective emb :=
    fun _ _ h ↦ Subtype.ext (congrArg (fun x : Nat.smoothNumbers (Y+1) ↦ x.val) h)
  simpa only [Function.comp_def, emb] using (summable_reciprocal_smoothNumbers Y).comp_injective he

private theorem smoothSubset_reciprocal_le {Y : ℕ} {D : Set ℕ}
    (hD : D ⊆ Nat.smoothNumbers (Y+1)) :
    (∑' s : D, (s.val:ℝ)⁻¹) ≤ (integerSmoothDensityFactor Y)⁻¹ := by
  let emb : D → Nat.smoothNumbers (Y+1) := fun x ↦ ⟨x.val,hD x.property⟩
  have he : Function.Injective emb :=
    fun _ _ h ↦ Subtype.ext (congrArg (fun x : Nat.smoothNumbers (Y+1) ↦ x.val) h)
  rw [← (hasSum_reciprocal_smoothNumbers Y).tsum_eq]
  exact Summable.tsum_le_tsum_of_inj emb he (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl)
    (smoothSubset_reciprocal_summable hD) (summable_reciprocal_smoothNumbers Y)

private theorem prefixSlice_mem {A : Set ℕ} {n N : ℕ} :
    n ∈ integerPrefixSlice A N ↔ 1 ≤ n ∧ n ≤ N ∧ n ∈ A := by
  simp only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc, and_assoc]

private theorem finiteSmoothFiber_reciprocal_le (A : Set ℕ) (Y N r : ℕ) :
    (∑ n ∈ (integerPrefixSlice A N).filter (fun n ↦ integerRoughPart Y n = r),
      (n:ℝ)⁻¹) ≤ (r:ℝ)⁻¹ * ∑' s : smoothFiber A Y r, (s.val:ℝ)⁻¹ := by
  let T := (integerPrefixSlice A N).filter (fun n ↦ integerRoughPart Y n = r)
  have readBack {n : ℕ} (hn : n ∈ T) : r * integerSmoothPart Y n = n := by
    obtain ⟨h₁, h₂⟩ := mem_filter.mp hn
    have hpos := (prefixSlice_mem.mp h₁).1
    have h := integerSmoothPart_mul_roughPart Y (Nat.ne_of_gt hpos)
    rwa [h₂, mul_comm] at h
  let f : ↥T → smoothFiber A Y r := fun n ↦ ⟨integerSmoothPart Y n.val,
    integerSmoothPart_mem Y n.val, by
      rw [readBack n.property]
      exact (prefixSlice_mem.mp (mem_filter.mp n.property).1).2.2⟩
  have hfi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have he : integerSmoothPart Y a.val = integerSmoothPart Y b.val :=
      congrArg (fun x : smoothFiber A Y r ↦ x.val) h
    exact (readBack a.property).symm.trans ((congrArg (fun s : ℕ ↦ r*s) he).trans (readBack b.property))
  have hs : Summable (fun s : smoothFiber A Y r ↦ (s.val:ℝ)⁻¹) :=
    smoothSubset_reciprocal_summable (fun _ h ↦ h.1)
  have hm := hs.sum_le_tsum (Finset.univ.map ⟨f,hfi⟩) (fun _ _ ↦ by positivity)
  rw [Finset.sum_map, Finset.univ_eq_attach] at hm
  change (∑ n ∈ T.attach, (integerSmoothPart Y n.val : ℝ)⁻¹) ≤ _ at hm
  rw [Finset.sum_attach T (fun n : ℕ ↦ (integerSmoothPart Y n : ℝ)⁻¹)] at hm
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hm (by positivity))
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hn' := congrArg (fun x : ℕ ↦ (x:ℝ)⁻¹) (readBack hn).symm
  simpa only [Nat.cast_mul, mul_inv_rev, mul_comm] using hn'.le

/-- Finite reciprocal mass is bounded by the rough reciprocal mass times
the supremal fixed smooth-fiber weight. -/
theorem reciprocalMassUpTo_le_smoothLower (integral : Bool) (Y : ℕ)
    {A : Set ℕ} (hA : IntegerPrefixAdmissible integral A) (N : ℕ) :
    reciprocalMassUpTo A N ≤
      (integerSmoothLowerOptimization integral Y / integerSmoothDensityFactor Y) *
        reciprocalMassUpTo (integerRoughNumbers Y) N := by
  let W : Set ℝ := {w | ∃ D : Set ℕ, D ⊆ Nat.smoothNumbers (Y+1) ∧
    IntegerPrefixAdmissible integral D ∧ w = ∑' s : D, (s.val:ℝ)⁻¹}
  have hW : BddAbove W := by
    refine ⟨(integerSmoothDensityFactor Y)⁻¹, ?_⟩
    rintro w ⟨D, hD, _, rfl⟩
    exact smoothSubset_reciprocal_le hD
  have heq : integerSmoothLowerOptimization integral Y / integerSmoothDensityFactor Y = sSup W := by
    change integerSmoothDensityFactor Y * sSup W / integerSmoothDensityFactor Y = _
    rw [mul_comm, mul_div_cancel_right₀ _ (integerSmoothDensityFactor_pos Y).ne']
  have hmaps (n : ℕ) (hn : n ∈ integerPrefixSlice A N) :
      integerRoughPart Y n ∈ integerPrefixSlice (integerRoughNumbers Y) N := by
    obtain ⟨hn₀, hnN, _⟩ := prefixSlice_mem.mp hn
    have hr := integerRoughPart_mem Y n
    have hdiv : integerRoughPart Y n ∣ n := by
      refine ⟨integerSmoothPart Y n, ?_⟩
      rw [mul_comm, integerSmoothPart_mul_roughPart Y (Nat.ne_of_gt hn₀)]
    exact prefixSlice_mem.mpr
      ⟨Nat.pos_of_ne_zero hr.1, (Nat.le_of_dvd hn₀ hdiv).trans hnN, hr⟩
  rw [heq]
  simp only [reciprocalMassUpTo]
  rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
  apply sum_le_sum
  intro r hr
  have hr' := (prefixSlice_mem.mp hr).1
  have hsub : smoothFiber A Y r ⊆ Nat.smoothNumbers (Y+1) := fun _ h ↦ h.1
  have hsup : (∑' s : smoothFiber A Y r, (s.val:ℝ)⁻¹) ≤ sSup W := by
    exact le_csSup hW ⟨smoothFiber A Y r, hsub, smoothFiber_admissible hA hr', rfl⟩
  exact (finiteSmoothFiber_reciprocal_le A Y N r).trans
    ((mul_le_mul_of_nonneg_left hsup (by positivity)).trans_eq (mul_comm _ _))

/-- Every admissible set with a natural density is bounded by the same
fixed-set smooth optimization. -/
theorem naturalDensity_le_integerSmoothLowerOptimization (integral : Bool) (Y : ℕ)
    {A : Set ℕ} {d : ℝ} (hA : IntegerPrefixAdmissible integral A)
    (hd : HasNaturalDensity A d) :
    d ≤ integerSmoothLowerOptimization integral Y := by
  have h := naturalDensity_le_of_reciprocalMass_le hd (hasNaturalDensity_integerRoughNumbers Y)
    (reciprocalMassUpTo_le_smoothLower integral Y hA)
  rwa [div_mul_cancel₀ _ (integerSmoothDensityFactor_pos Y).ne'] at h

/-- The article's bound `b_ℚ ≤ B`, for either convention. -/
theorem integerNaturalDensitySupremum_le_smoothLower (integral : Bool) (Y : ℕ) :
    integerNaturalDensitySupremum integral ≤ integerSmoothLowerOptimization integral Y := by
  unfold integerNaturalDensitySupremum
  apply csSup_le
  · exact ⟨0, ∅, by simp, by intro a b c ha; exact ha.elim, hasNaturalDensity_empty⟩
  · rintro d ⟨A, _, hA, hd⟩
    exact naturalDensity_le_integerSmoothLowerOptimization integral Y hA hd

end GRHArticle.ProgressionFree
