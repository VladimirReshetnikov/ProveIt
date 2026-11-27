import GRHArticle.ProgressionFree.LogarithmicAverages
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealPurePowerExchange
import GRHArticle.ProgressionFree.NumberFieldIdeals.UniformCounts

/-!
# Logarithmic density in number fields

Summation by parts includes the entire norm layer at each integer cutoff.
For every set with relative natural density, the reciprocal-norm sum has
leading coefficient equal to that density times the residue of the
Dedekind zeta function.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

noncomputable def idealNormPrefix (A : Set (Ideal (𝓞 K))⁰) (N : ℕ) : Finset (Ideal (𝓞 K))⁰ :=
  (idealNormCutoff_finite A N).toFinset

@[simp] theorem mem_idealNormPrefix {A : Set (Ideal (𝓞 K))⁰} {N : ℕ} {I : (Ideal (𝓞 K))⁰} :
    I ∈ idealNormPrefix A N ↔ I ∈ A ∧ absNorm I.val ≤ N := Set.Finite.mem_toFinset _

theorem card_idealNormPrefix (A : Set (Ideal (𝓞 K))⁰) (N : ℕ) :
    (idealNormPrefix A N).card = countUpTo A N := by
  rw [countUpTo_nat_eq_ncard, Set.ncard_eq_toFinset_card _ (idealNormCutoff_finite A N)]
  rfl

/-- Sum of the reciprocal norms through a given integer cutoff. -/
noncomputable def idealReciprocalMassUpTo (A : Set (Ideal (𝓞 K))⁰) (N : ℕ) : ℝ :=
  ∑ I ∈ idealNormPrefix A N, (absNorm I.val : ℝ)⁻¹

theorem idealReciprocalMassUpTo_partial_summation (A : Set (Ideal (𝓞 K))⁰) (N : ℕ) :
    idealReciprocalMassUpTo A N = (countUpTo A N : ℝ) / ((N:ℝ)+1) +
      ∑ k ∈ range N, ((countUpTo A (k+1 : ℕ) : ℝ) / ((k:ℝ)+1)) / ((k:ℝ)+2) := by
  classical
  induction N with
  | zero =>
    have he : idealNormPrefix A 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro I h
      have := (mem_idealNormPrefix.mp h).2
      have := absNorm_pos_of_nonZeroDivisors I
      omega
    simp [idealReciprocalMassUpTo, he, countUpTo_zero_of_lt_one A (by norm_num : (0:ℝ)<1)]
  | succ N ih =>
    let T := idealNormPrefix A (N+1) \ idealNormPrefix A N
    have hsub : idealNormPrefix A N ⊆ idealNormPrefix A (N+1) := by
      intro I h
      exact mem_idealNormPrefix.mpr ⟨(mem_idealNormPrefix.mp h).1,
        (mem_idealNormPrefix.mp h).2.trans (Nat.le_succ _)⟩
    have hnorm I (hI : I ∈ T) : absNorm I.val = N+1 := by
      obtain ⟨ha,hb⟩ := mem_sdiff.mp hI
      have h₁ := mem_idealNormPrefix.mp ha
      have h₂ : ¬absNorm I.val ≤ N := fun h ↦ hb (mem_idealNormPrefix.mpr ⟨h₁.1,h⟩)
      omega
    have hmass : idealReciprocalMassUpTo A (N+1) =
        idealReciprocalMassUpTo A N + (T.card : ℝ) / ((N:ℝ)+1) := by
      have he := sum_sdiff hsub (f := fun I : (Ideal (𝓞 K))⁰ ↦ (absNorm I.val : ℝ)⁻¹)
      change (∑ I ∈ T, _) + idealReciprocalMassUpTo A N = idealReciprocalMassUpTo A (N+1) at he
      rw [← he, add_comm]
      congr 1
      calc
        _ = ∑ _ ∈ T, (((N+1 : ℕ) : ℝ))⁻¹ := sum_congr rfl fun I hi ↦ by rw [hnorm I hi]
        _ = _ := by simp [div_eq_mul_inv]
    have hc : (countUpTo A (N+1 : ℕ) : ℝ) = (countUpTo A N : ℝ) + T.card := by
      simp only [← card_idealNormPrefix, ← Nat.cast_add]
      have hcard : (idealNormPrefix A N).card + T.card = (idealNormPrefix A (N+1)).card := by
        simpa [T,Nat.add_comm] using card_sdiff_add_card_eq_card hsub
      exact_mod_cast hcard.symm
    rw [hmass, ih, sum_range_succ, hc]
    push_cast
    have h₁ : (N:ℝ)+1 ≠ 0 := by positivity
    have h₂ : (N:ℝ)+2 ≠ 0 := by positivity
    rw [show (N:ℝ)+1+1 = (N:ℝ)+2 by ring]
    field_simp
    ring

/-- Natural density gives the exact logarithmic asymptotic, with the
Dedekind zeta residue as the normalization for all ideals. -/
theorem tendsto_idealReciprocalMassUpTo_div_log {A : Set (Ideal (𝓞 K))⁰} {d : ℝ}
    (hd : HasNaturalDensity A d) :
    Tendsto (fun N : ℕ ↦ idealReciprocalMassUpTo A N / Real.log N) atTop (𝓝 (d * dedekindZeta_residue K)) := by
  let f (N : ℕ) := (countUpTo A (N:ℝ) : ℝ) / (N:ℝ)
  have hf : Tendsto f atTop (𝓝 (d * dedekindZeta_residue K)) :=
    ((hasNaturalDensity_iff_tendsto_div A d).mp hd).comp tendsto_natCast_atTop_atTop
  have hm := tendsto_logarithmicAverage_of_tendsto (hf.comp (tendsto_add_atTop_nat 1))
  obtain ⟨C,hC,hCount⟩ := exists_uniform_countUpTo_bound (K := K)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb : Tendsto (fun N : ℕ ↦ (countUpTo A N : ℝ) / ((N:ℝ)+1) / Real.log N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlog.const_div_atTop C)
    · filter_upwards [eventually_gt_atTop 1] with N hN
      exact div_nonneg (by positivity) (Real.log_pos (by exact_mod_cast hN)).le
    · filter_upwards [eventually_gt_atTop 1] with N hN
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by exact_mod_cast hN)).le
      apply (div_le_iff₀ (by positivity)).mpr
      have hc := countUpTo_mono (Set.subset_univ A) (le_refl (N : ℝ)) (Nat.cast_nonneg N)
      have hu := hCount (N:ℝ) (Nat.cast_nonneg N)
      exact (Nat.cast_le.mpr hc).trans (hu.trans (by nlinarith))
  have h := hb.add hm
  rw [zero_add] at h
  refine h.congr fun N ↦ ?_
  simp only [idealReciprocalMassUpTo_partial_summation, add_div, Function.comp_apply, f, Nat.cast_add, Nat.cast_one]

end GRHArticle.ProgressionFree.NumberFieldIdeals
