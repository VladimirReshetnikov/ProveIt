import GRHArticle.ProgressionFree.IntegerDivisibilityExpansion
import GRHArticle.ProgressionFree.IntegerLargestPrimeDilations

/-!
# Uniform smooth-number estimates for finite divisibility rules

A fixed positive divisor can be absorbed into the largest-prime cutoff.
The uniform dilation estimate then lets the corresponding divisibility
condition contribute its usual density even with a moving smooth cutoff.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Finset
open scoped Classical BigOperators

private theorem countUpTo_dvd_inter_smooth {d Y : ℕ} (hd : 0 < d) (hdY : d ≤ Y) (N : ℕ) :
    countUpTo ({n | d ∣ n} ∩ Nat.smoothNumbers (Y+1)) N =
      countUpTo (Nat.smoothNumbers (Y+1)) (N/d) := by
  let S := Nat.smoothNumbers (Y+1)
  have hdS : d ∈ S := ⟨hd.ne', fun p hp ↦
    Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactorsList hp).trans hdY)⟩
  change (integerPrefixSlice ({n | d ∣ n} ∩ S) N).card =
    (integerPrefixSlice S (N/d)).card
  symm
  apply Finset.card_bij (fun k _ ↦ d*k)
  · intro k hk
    simp only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc, Set.mem_inter_iff,
      Set.mem_setOf_eq] at hk ⊢
    exact ⟨⟨Nat.mul_pos hd hk.1.1, by
      have h := (Nat.le_div_iff_mul_le hd).mp hk.1.2
      simpa only [mul_comm d k] using h⟩, dvd_mul_right _ _, Nat.mul_mem_smoothNumbers hdS hk.2⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · intro n hn
    simp only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc, Set.mem_inter_iff,
      Set.mem_setOf_eq] at hn
    obtain ⟨⟨hn0, hnN⟩, ⟨k, rfl⟩, hnS⟩ := hn
    refine ⟨k, ?_, rfl⟩
    simp only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc]
    refine ⟨⟨?_, (Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm d k] using hnN)⟩,
      Nat.mem_smoothNumbers_of_dvd hnS (dvd_mul_left _ _)⟩
    by_contra! hk
    have hk' : k = 0 := by omega
    simp [hk'] at hn0

private def UniformSmoothError (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ N Y : ℕ, M ≤ N → M ≤ Y → |f N Y| < ε

namespace UniformSmoothError

theorem zero : UniformSmoothError (fun _ _ ↦ 0) := by
  intro ε hε
  exact ⟨0, fun _ _ _ _ ↦ by simpa using hε⟩

theorem add {f g : ℕ → ℕ → ℝ} (hf : UniformSmoothError f) (hg : UniformSmoothError g) :
    UniformSmoothError (fun N Y ↦ f N Y + g N Y) := by
  intro ε hε
  obtain ⟨M, hM⟩ := hf (ε/2) (by positivity)
  obtain ⟨K, hK⟩ := hg (ε/2) (by positivity)
  refine ⟨max M K, fun N Y hN hY ↦ (abs_add_le _ _).trans_lt ?_⟩
  have hf' := hM N Y ((le_max_left _ _).trans hN) ((le_max_left _ _).trans hY)
  have hg' := hK N Y ((le_max_right _ _).trans hN) ((le_max_right _ _).trans hY)
  linarith

theorem const_mul {f : ℕ → ℕ → ℝ} (hf : UniformSmoothError f) (c : ℝ) :
    UniformSmoothError (fun N Y ↦ c * f N Y) := by
  intro ε hε
  have hc : 0 < |c| + 1 := by positivity
  obtain ⟨M, hM⟩ := hf (ε / (|c| + 1)) (div_pos hε hc)
  refine ⟨M, fun N Y hN hY ↦ ?_⟩
  rw [abs_mul]
  refine (mul_le_mul_of_nonneg_right (show |c| ≤ |c| + 1 by linarith)
    (abs_nonneg _)).trans_lt ?_
  rw [mul_comm]
  exact (lt_div_iff₀ hc).mp (hM N Y hN hY)

end UniformSmoothError

private theorem uniformSmoothError_dvd {d : ℕ} (hd : 0 < d) :
    UniformSmoothError (fun N Y ↦ densityUpTo ({n | d ∣ n} ∩ Nat.smoothNumbers (Y+1)) N -
      (1 / (d : ℝ)) * densityUpTo (Nat.smoothNumbers (Y+1)) N) := by
  intro ε hε
  have hdens := hasNaturalDensity_dvd d hd
  have hratio : ∀ᶠ N : ℕ in atTop, |((N/d : ℕ) : ℝ)/N - 1/(d : ℝ)| < ε/2 := by
    apply (hdens.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε/2))).mono
    intro N h
    change dist (densityUpTo {n | d ∣ n} N) (1/(d : ℝ)) < ε/2 at h
    simpa only [Real.dist_eq, densityUpTo, countUpTo_dvd d N hd] using h
  obtain ⟨M, hM⟩ := eventually_atTop.1 <|
    (eventually_abs_densityUpTo_smooth_div_sub_lt hd (show 0 < ε/2 by positivity)).and hratio
  refine ⟨max M d, fun N Y hN hY ↦ ?_⟩
  let S := Nat.smoothNumbers (Y+1)
  let α := ((N/d : ℕ) : ℝ)/N
  let x := densityUpTo S (N/d)
  let y := densityUpTo S N
  have hN' := (le_max_right M d).trans hN
  have hY' := (le_max_right M d).trans hY
  have hNpos := hd.trans_le hN'
  have hMpos : 0 < N/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hN')
  have hM0 : ((N/d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    dsimp [α]
    exact (div_le_one (by exact_mod_cast hNpos)).2 (by exact_mod_cast Nat.div_le_self N d)
  have hy0 : 0 ≤ y := densityUpTo_nonneg _ _
  have hy1 : y ≤ 1 := densityUpTo_le_one _ _
  have heq : densityUpTo ({n | d ∣ n} ∩ S) N = α*x := by
    unfold densityUpTo
    rw [countUpTo_dvd_inter_smooth hd hY' N]
    change (countUpTo S (N/d) : ℝ)/N =
      (((N/d : ℕ) : ℝ)/N) * ((countUpTo S (N/d) : ℝ)/((N/d : ℕ) : ℝ))
    rw [div_mul_div_comm, mul_comm (((N/d : ℕ) : ℝ)), mul_div_mul_right _ _ hM0]
  have hsum := hM N ((le_max_left M d).trans hN)
  change |densityUpTo ({n | d ∣ n} ∩ S) N - (1 / (d : ℝ)) * y| < ε
  rw [heq, show α*x - (1/(d : ℝ))*y = α*(x-y) + (α-1/(d : ℝ))*y by ring]
  refine (abs_add_le _ _).trans_lt ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg hy0]
  have hα := mul_le_of_le_one_left (abs_nonneg (x-y)) hα1
  have hy := mul_le_of_le_one_right (abs_nonneg (α-1/(d : ℝ))) hy1
  exact (add_le_add hα hy).trans_lt (by linarith [hsum.1 Y, hsum.2])

private theorem uniformSmoothError_sum (L : List (ℕ × ℝ)) (hp : ∀ t ∈ L, 0 < t.1) :
    UniformSmoothError (fun N Y ↦
      (L.map fun t ↦ t.2 * densityUpTo ({n | t.1 ∣ n} ∩ Nat.smoothNumbers (Y+1)) N).sum -
      (L.map fun t ↦ t.2 * (1/(t.1 : ℝ))).sum * densityUpTo (Nat.smoothNumbers (Y+1)) N) := by
  induction L with
  | nil => simpa using UniformSmoothError.zero
  | cons t L ih =>
    have h := (uniformSmoothError_dvd (hp t (List.mem_cons_self ..))).const_mul t.2
    specialize ih (fun s hs ↦ hp s (List.mem_cons_of_mem _ hs))
    have h' := UniformSmoothError.add h ih
    simpa only [List.map_cons, List.sum_cons, add_mul, mul_sub, mul_assoc, add_sub_add_comm] using h'

/-- Uniform asymptotic independence from smoothness for a set with density `d`. -/
def HasUniformSmoothDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ N Y : ℕ, M ≤ N → M ≤ Y →
    |densityUpTo (A ∩ Nat.smoothNumbers (Y+1)) N - d * densityUpTo (Nat.smoothNumbers (Y+1)) N| < ε

private theorem smooth_contains_prefix (N : ℕ) :
    ∀ n ∈ Icc 1 N, n ∈ Nat.smoothNumbers (N+1) := by
  intro n hn
  obtain ⟨h1,hN⟩ := mem_Icc.mp hn
  exact ⟨Nat.ne_of_gt h1, fun p hp ↦
    Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactorsList hp).trans hN)⟩

theorem HasUniformSmoothDensity.hasNaturalDensity {A : Set ℕ} {d : ℝ}
    (h : HasUniformSmoothDensity A d) : HasNaturalDensity A d := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  refine ⟨max 1 M, fun N hN ↦ ?_⟩
  have h1 := (le_max_left 1 M).trans hN
  have hN' := (le_max_right 1 M).trans hN
  have hsub : densityUpTo (A ∩ Nat.smoothNumbers (N+1)) N = densityUpTo A N :=
    le_antisymm (densityUpTo_mono Set.inter_subset_left _) (densityUpTo_le_of_subset_on_cutoff N
      fun n hn ha ↦ ⟨ha, smooth_contains_prefix N n hn⟩)
  have hfull : densityUpTo (Nat.smoothNumbers (N+1)) N = 1 := by
    have hle := densityUpTo_le_of_subset_on_cutoff N
      (s := Set.univ) (t := Nat.smoothNumbers (N+1)) (fun n hn _ ↦ smooth_contains_prefix N n hn)
    have huniv : densityUpTo Set.univ N = 1 := by
      unfold densityUpTo countUpTo
      simp [Nat.card_Icc, show (N : ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
    exact le_antisymm (densityUpTo_le_one _ _) (huniv ▸ hle)
  rw [Real.dist_eq]
  simpa only [hsub, hfull, mul_one] using hM N N hN' hN'

/-- A finite linear combination of divisibility tests has a uniform smoothness
estimate with its ordinary natural density. -/
theorem IntegerDivisibilityExpansion.exists_hasUniformSmoothDensity {A : Set ℕ}
    (hA : IntegerDivisibilityExpansion A) : ∃ d, HasUniformSmoothDensity A d := by
  obtain ⟨L, hp, he⟩ := hA.exists_densityUpTo_inter_eq
  refine ⟨(L.map fun t ↦ t.2*(1/(t.1 : ℝ))).sum, ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := uniformSmoothError_sum L hp ε hε
  exact ⟨M, fun N Y hN hY ↦ he (Nat.smoothNumbers (Y+1)) N ▸ hM N Y hN hY⟩

end GRHArticle.ProgressionFree
