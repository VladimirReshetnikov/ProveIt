import GRHArticle.ProgressionFree.NumberFieldIdeals.UniformCounts
import GRHArticle.ProgressionFree.NumberFieldIdeals.LocalFactors
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The inverse-square norm tail

Group nonzero ideals by norm. Their cumulative multiplicities are
linear in the cutoff, so the nonnegative Dirichlet series converges
at two. Restricting it to prime ideals gives the tail required for
passing from finite prime conditions to infinitely many.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Filter Topology NumberField Ideal Finset IsDedekindDomain
open scoped nonZeroDivisors Asymptotics

variable {K : Type*} [Field K] [NumberField K]

/-- The reciprocal squared norms of all nonzero integral ideals are summable. -/
theorem summable_inv_sq_absNorm :
    Summable fun I : (Ideal (𝓞 K))⁰ ↦ ((absNorm I.val : ℝ)^2)⁻¹ := by
  classical
  let ν (I : (Ideal (𝓞 K))⁰) := absNorm I.val
  let F (n : ℕ) := {I : (Ideal (𝓞 K))⁰ | ν I = n}
  let a (n : ℕ) : ℝ := Nat.card (F n)
  have hF n : (F n).Finite := (finite_setOf_absNorm_le₀ (S := 𝓞 K) n).subset
    (fun _ hn ↦ (show ν _ = n from hn).le)
  have ha (N : ℕ) : ∑ n ∈ Icc 1 N, a n = (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) N : ℝ) := by
    simp only [a, ← Nat.cast_sum]
    congr 1
    change (∑ n ∈ Icc 1 N, Nat.card {I // ν I = n}) = _
    rw [← Finset.card_preimage_eq_sum_card_image_eq (f := ν) (fun k _ ↦ hF k)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro I
    simp [ν]
    exact fun _ ↦ absNorm_pos_of_nonZeroDivisors I
  obtain ⟨C,_,hC⟩ := exists_uniform_countUpTo_bound (K := K)
  have hO : (fun N ↦ ∑ n ∈ Icc 1 N, a n) =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ (1:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards with N
    rw [ha, Real.rpow_one, Real.norm_natCast, Real.norm_natCast]
    exact hC _ (Nat.cast_nonneg _)
  have hs := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (2:ℂ)) hO
    (fun n ↦ Nat.cast_nonneg _) (by norm_num) (by norm_num)
  have hweight : Summable fun n : ℕ ↦ a n / (n : ℝ)^2 := by
    refine hs.norm.congr fun n ↦ ?_
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · simp [hn]
    · simp [Complex.norm_real, Real.norm_of_nonneg (show (0:ℝ) ≤ a n from Nat.cast_nonneg _)]
  apply (summable_partition (s := F) (fun I ↦ by positivity)
    (fun I ↦ ⟨ν I,rfl,fun _ h ↦ h.symm⟩)).mpr
  constructor
  · intro n
    letI := (hF n).fintype
    exact (hasSum_fintype _).summable
  · exact hweight.congr fun n ↦ by
      letI := (hF n).fintype
      have hn (I : F n) : absNorm I.val.val = n := I.property
      simp only [hn,tsum_fintype, sum_const,card_univ,nsmul_eq_mul, a,Nat.card_eq_fintype_card,
        div_eq_mul_inv]

/-- The prime-ideal inverse-square series converges in every number field. -/
theorem summable_primeIdeal_inv_sq_absNorm :
    Summable fun p : HeightOneSpectrum (𝓞 K) ↦ ((absNorm p.asIdeal : ℝ)^2)⁻¹ := by
  let f (I : (Ideal (𝓞 K))⁰) : ℝ := ((absNorm I.val : ℝ)^2)⁻¹
  have hs : Summable f := summable_inv_sq_absNorm
  have hinj : Function.Injective (primeIdeal (K := K)) := by
    intro p q he
    apply HeightOneSpectrum.ext
    exact congrArg (fun J : (Ideal (𝓞 K))⁰ ↦ J.val) he
  change Summable (f ∘ primeIdeal)
  exact hs.comp_injective hinj

end GRHArticle.ProgressionFree.NumberFieldIdeals
