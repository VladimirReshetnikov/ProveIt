import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughParts
import GRHArticle.ProgressionFree.NumberFieldIdeals.LogarithmicDensity
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothNaturalLowerBound

/-!
# Bounding global natural density by the smooth optimization

Sum reciprocal ideal norms one rough fiber at a time. Each smooth fiber
of an admissible set is admissible. The resulting inequality between
finite sums passes to natural densities by logarithmic averaging.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem finiteFiber_weight_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : Set (Ideal (𝓞 K))⁰) (N : ℕ) (r : (Ideal (𝓞 K))⁰) :
    (∑ I ∈ (idealNormPrefix A N).filter (fun I ↦ idealRoughPart S I = r), (absNorm I.val : ℝ)⁻¹)
      ≤ (absNorm r.val : ℝ)⁻¹ * idealReciprocalWeight (K := K) (idealSmoothFiber S A r) := by
  classical
  let T := (idealNormPrefix A N).filter (fun I ↦ idealRoughPart S I = r)
  have hrec I (hI : I ∈ T) : r * idealSmoothPart S I = I := by
    simpa only [(mem_filter.mp hI).2] using idealRoughPart_mul_smoothPart S I
  let f : T → idealSmoothFiber S A r := fun I ↦ ⟨idealSmoothPart S I.val, idealSmoothPart_mem S _,
    by rw [hrec _ I.property]; exact (mem_idealNormPrefix.mp (mem_filter.mp I.property).1).1⟩
  have hi : Function.Injective f := by
    intro I J he
    apply Subtype.ext
    have hs : idealSmoothPart S I.val = idealSmoothPart S J.val := congrArg Subtype.val he
    exact (hrec _ I.property).symm.trans ((congrArg (r * ·) hs).trans (hrec _ J.property))
  have hs := summable_reciprocal_smoothIdealSubset (idealSmoothFiber_subset_range S A r)
  have hm := hs.sum_le_tsum (Finset.univ.map ⟨f,hi⟩) (fun _ _ ↦ by positivity)
  rw [sum_map, univ_eq_attach] at hm
  change (∑ I ∈ T.attach, (absNorm (idealSmoothPart S I.val).val : ℝ)⁻¹) ≤ _ at hm
  rw [sum_attach T (fun I ↦ (absNorm (idealSmoothPart S I).val : ℝ)⁻¹)] at hm
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hm (by positivity))
  rw [mul_sum]
  apply sum_le_sum
  intro I hI
  have he := congrArg (fun J : (Ideal (𝓞 K))⁰ ↦ (absNorm J.val : ℝ)⁻¹) (hrec I hI).symm
  simpa only [Submonoid.coe_mul,map_mul,Nat.cast_mul,mul_inv_rev,mul_comm] using he.le

/-- Any uniform bound on the reciprocal mass of an individual smooth
fiber gives an inequality at every finite cutoff. -/
theorem idealReciprocalMassUpTo_le_of_fiber_bound (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : Set (Ideal (𝓞 K))⁰) {M : ℝ}
    (hM : ∀ r ∈ roughIdeals S, idealReciprocalWeight (K := K) (idealSmoothFiber S A r) ≤ M) (N : ℕ) :
    idealReciprocalMassUpTo A N ≤ M * idealReciprocalMassUpTo (roughIdeals S) N := by
  classical
  have hmap : ∀ I ∈ idealNormPrefix A N, idealRoughPart S I ∈ idealNormPrefix (roughIdeals S) N := by
    intro I hI
    apply mem_idealNormPrefix.mpr
    refine ⟨idealRoughPart_mem S I, le_trans ?_ (mem_idealNormPrefix.mp hI).2⟩
    have hn := congrArg (fun J : (Ideal (𝓞 K))⁰ ↦ absNorm J.val) (idealRoughPart_mul_smoothPart S I)
    simp only [Submonoid.coe_mul,map_mul] at hn
    rw [← hn]
    exact Nat.le_mul_of_pos_right _ (absNorm_pos_of_nonZeroDivisors _)
  unfold idealReciprocalMassUpTo
  rw [← sum_fiberwise_of_maps_to hmap, mul_sum]
  apply sum_le_sum
  intro r hr
  exact (finiteFiber_weight_le S A N r).trans
    ((mul_le_mul_of_nonneg_left (hM _ (mem_idealNormPrefix.mp hr).1) (by positivity)).trans_eq (mul_comm _ _))

/-- The natural density of every admissible set is bounded by the fixed
smooth-template optimization. -/
theorem idealNaturalDensity_le_smoothLowerOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {A : Set (Ideal (𝓞 K))⁰} {d : ℝ}
    (hA : IdealAdmissible integral A) (hd : HasNaturalDensity A d) :
    d ≤ idealSmoothLowerOptimization integral S := by
  let c := idealSmoothDensityFactor S
  let B := idealSmoothLowerOptimization integral S
  have hc : 0 < c := idealSmoothDensityFactor_pos S
  have hf r (_ : r ∈ roughIdeals S) : idealReciprocalWeight (K := K) (idealSmoothFiber S A r) ≤ B/c := by
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm]
    exact idealSmoothDensityFactor_mul_weight_le_lowerOptimization
      (idealSmoothFiber_subset_range S A r) (idealAdmissible_idealSmoothFiber S hA r)
  have h₁ := tendsto_idealReciprocalMassUpTo_div_log hd
  have h₂ := (tendsto_idealReciprocalMassUpTo_div_log (hasNaturalDensity_roughIdeals S)).const_mul (B/c)
  have h : d * dedekindZeta_residue K ≤ (B/c) * (c * dedekindZeta_residue K) := by
    apply le_of_tendsto_of_tendsto h₁ h₂
    filter_upwards [eventually_gt_atTop 1] with N hN
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (idealReciprocalMassUpTo_le_of_fiber_bound S A hf N)
      (Real.log_pos (by exact_mod_cast hN)).le
  rwa [← mul_assoc, div_mul_cancel₀ _ hc.ne', mul_le_mul_iff_left₀ (dedekindZeta_residue_pos K)] at h

/-- The article's global bound `b_K ≤ B` for every finite smooth prime set. -/
theorem idealNaturalDensitySupremum_le_smoothLowerOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealNaturalDensitySupremum K integral ≤ idealSmoothLowerOptimization integral S := by
  apply csSup_le
  · refine ⟨0,∅,fun _ _ _ ha ↦ ha.elim,?_⟩
    have he : densityUpTo (∅ : Set (Ideal (𝓞 K))⁰) = fun _ ↦ 0 := by
      funext X
      simp [densityUpTo,countUpTo]
    simp [HasNaturalDensity,he]
  · rintro _ ⟨A,hA,hd⟩
    exact idealNaturalDensity_le_smoothLowerOptimization integral S hA hd

end GRHArticle.ProgressionFree.NumberFieldIdeals
