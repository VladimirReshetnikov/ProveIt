import GRHArticle.ProgressionFree.PrimeBlockRuleDensity
import GRHArticle.ProgressionFree.IntegerPrimeBlockPartitions

/-!
# Density of arbitrary independent rules at finitely many primes

Truncation at exponent `K` changes membership only at multiples of the
finitely many prime powers `p^K`. Their total contribution tends to zero,
and each exact truncated factor converges to the full exponent mass.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped BigOperators

/-- The reciprocal mass of an exponent rule with scalar weight `r`. -/
noncomputable def exponentRuleMass (r : ℝ) (R : Set ℕ) : ℝ :=
  ∑' e : R, r^e.val

/-- The set imposing independent rules at only the specified primes. -/
def integerFiniteIndependentPrimeRules (P : Finset ℕ) (R : ℕ → Set ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p : ↥P, n.factorization p.val ∈ R p.val}

private def truncatedRules (P : Finset ℕ) (R : ℕ → Set ℕ) (K : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p : ↥P, n.factorization p.val ∈ exponentsBelow (R p.val) K}

private theorem densityUpTo_truncation_error (P : Finset ℕ) (R : ℕ → Set ℕ)
    (hP : ∀ p ∈ P, p.Prime) (K N : ℕ) :
    |densityUpTo (integerFiniteIndependentPrimeRules P R) N -
      densityUpTo (truncatedRules P R K) N| ≤ ∑ p ∈ P, 1/(p : ℝ)^K := by
  classical
  have hsub : truncatedRules P R K ⊆ integerFiniteIndependentPrimeRules P R := by
    rintro n ⟨hn,h⟩
    exact ⟨hn,fun p ↦ (mem_exponentsBelow.mp (h p)).1⟩
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset
    (E := {n | ∃ p ∈ P, p^K ∣ n}) N ?_).trans ?_
  · intro n hn
    rcases hn with ⟨hn,hcut⟩ | ⟨hcut,hn⟩
    · by_contra h
      apply hcut
      refine ⟨hn.1,fun p ↦ mem_exponentsBelow.mpr ⟨hn.2 p,?_⟩⟩
      by_contra! he
      exact h ⟨p.val,p.property,((hP _ p.property).pow_dvd_iff_le_factorization hn.1).mpr he⟩
    · exact (hn (hsub hcut)).elim
  · simpa only [Nat.cast_pow] using
      densityUpTo_divisibleByOneOf_le P (fun p ↦ p^K) N
        (fun p hp ↦ pow_pos (hP p hp).pos _)

private theorem reciprocalPrime_lt_one {p : ℕ} (hp : p.Prime) : 1/(p : ℝ) < 1 :=
  (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

private theorem tendsto_exponentsBelow_mass {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (R : Set ℕ) :
    Tendsto (fun K ↦ ∑ e ∈ exponentsBelow R K, r^e) atTop (𝓝 (exponentRuleMass r R)) := by
  classical
  have hs : Summable (R.indicator fun n : ℕ ↦ r^n) :=
    summable_subtype_iff_indicator.mp ((hasSum_geometric_of_lt_one h0 h1).summable.subtype _)
  have ht := hs.hasSum.tendsto_sum_nat
  rw [← _root_.tsum_subtype] at ht
  refine ht.congr fun K ↦ ?_
  simp only [exponentsBelow,sum_filter,Set.indicator]

/-- Exact product density for arbitrary, possibly infinite, exponent
sets at finitely many distinct primes. -/
theorem hasNaturalDensity_integerFiniteIndependentPrimeRules (P : Finset ℕ)
    (R : ℕ → Set ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasNaturalDensity (integerFiniteIndependentPrimeRules P R)
      (∏ p : ↥P, (1-1/(p.val : ℝ))*exponentRuleMass (1/(p.val : ℝ)) (R p.val)) := by
  let d := ∏ p : ↥P, (1-1/(p.val : ℝ))*exponentRuleMass (1/(p.val : ℝ)) (R p.val)
  let dK (K : ℕ) := ∏ p : ↥P, (1-1/(p.val : ℝ))*
    ∑ e ∈ exponentsBelow (R p.val) K, (1/(p.val : ℝ))^e
  have hD : Tendsto dK atTop (𝓝 d) := by
    apply tendsto_finsetProd
    intro p _
    exact tendsto_const_nhds.mul
      (tendsto_exponentsBelow_mass (by positivity) (reciprocalPrime_lt_one (hP _ p.property)) _)
  have hErr : Tendsto (fun K : ℕ ↦ ∑ p ∈ P, 1/(p : ℝ)^K) atTop (𝓝 0) := by
    simp_rw [← one_div_pow]
    rw [show (0 : ℝ) = ∑ p ∈ P, 0 by simp]
    exact tendsto_finsetSum P fun p hp ↦
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (reciprocalPrime_lt_one (hP p hp))
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε₃ : 0 < ε/3 := by positivity
  have hDK : ∀ᶠ K in atTop, |dK K-d| < ε/3 :=
    (hD.eventually (Metric.ball_mem_nhds _ hε₃)).mono (fun K h ↦ by simpa [Metric.mem_ball,Real.dist_eq] using h)
  obtain ⟨K,hK,hdK⟩ := ((hErr.eventually_lt_const hε₃).and hDK).exists
  have hcut : HasNaturalDensity (truncatedRules P R K) (dK K) :=
    hasNaturalDensity_finite_prime_rules P (fun p ↦ exponentsBelow (R p.val) K) hP
  obtain ⟨N₀,hN₀⟩ := Metric.tendsto_atTop.1 hcut (ε/3) hε₃
  refine ⟨N₀, fun N hN ↦ ?_⟩
  rw [Real.dist_eq]
  have hT := densityUpTo_truncation_error P R hP K N
  have hC : |densityUpTo (truncatedRules P R K) N - dK K| < ε/3 := by
    simpa only [Real.dist_eq] using hN₀ N hN
  have hA := abs_sub_le (densityUpTo (integerFiniteIndependentPrimeRules P R) N)
    (densityUpTo (truncatedRules P R K) N) d
  have hB := abs_sub_le (densityUpTo (truncatedRules P R K) N) (dK K) d
  linarith

end GRHArticle.ProgressionFree
