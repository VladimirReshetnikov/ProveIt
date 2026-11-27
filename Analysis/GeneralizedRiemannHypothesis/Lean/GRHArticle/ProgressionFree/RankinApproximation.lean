import GRHArticle.ProgressionFree.DensityBounds
import GRHArticle.ProgressionFree.RankinTruncation
import Mathlib.NumberTheory.PrimeCounting

/-!
# Natural-density existence for Rankin's set

The two cutoffs affect the count only through large prime squares and high
powers of the finitely many tracked primes. Both errors can be made uniformly
small in the cutoff used to count positive integers.
-/

open Filter
open scoped BigOperators Topology

namespace GRHArticle.ProgressionFree

/-- Uniform error in the finite-prime, bounded-exponent approximation to
Rankin's set. -/
theorem abs_densityUpTo_rankin_sub_truncation_le (Y L N : ℕ) (hY : 0 < Y) :
    |densityUpTo rankinSet N - densityUpTo (rankinFiniteTruncation (Nat.primesLE Y) L) N| ≤
      1 / (Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ L := by
  let S := Nat.primesLE Y
  let E := {n : ℕ | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p ^ 2 ∣ n}
  let F := {n : ℕ | ∃ p ∈ S, p ^ L ∣ n}
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := Nat.prime_of_mem_primesLE hp
  have hcontains : (rankinSet \ rankinFiniteTruncation S L) ∪
      (rankinFiniteTruncation S L \ rankinSet) ⊆ E ∪ F := by
    intro n hn
    rcases rankinSet_symmDiff_rankinFiniteTruncation_subset S L hS hn with
      ⟨p, hp, hnot, hdiv⟩ | h
    · apply Or.inl
      exact ⟨p, lt_of_not_ge (fun h => hnot (Nat.mem_primesLE.mpr ⟨h, hp⟩)), hp, hdiv⟩
    · exact Or.inr h
  calc
    _ ≤ densityUpTo (E ∪ F) N := densityUpTo_abs_sub_le_of_symmDiff_subset N hcontains
    _ ≤ densityUpTo E N + densityUpTo F N := densityUpTo_union_le E F N
    _ ≤ _ := by
      apply add_le_add (densityUpTo_largePrimeSquare_le Y N hY)
      simpa only [F, S, Nat.cast_pow] using
        densityUpTo_divisibleByOneOf_le S (fun p => p ^ L) N
          (fun p hp => pow_pos (hS p hp).pos _)

private theorem tendsto_finitePrime_tail (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun L : ℕ => ∑ p ∈ S, 1 / (p : ℝ) ^ L) atTop (𝓝 0) := by
  have hpow (p : ℕ) (hp : p ∈ S) :
      Tendsto (fun L : ℕ => 1 / (p : ℝ) ^ L) atTop (𝓝 0) := by
    have hr : 1 < (p : ℝ) := by exact_mod_cast (hS p hp).one_lt
    have hu : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ (by linarith only [hr]), one_mul]
      exact hr
    simpa only [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hu
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum S hpow

/-- Rankin's progression-free set has a natural density. -/
theorem exists_hasNaturalDensity_rankinSet : ∃ d, HasNaturalDensity rankinSet d := by
  apply exists_hasNaturalDensity_of_uniform_approximation
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  have hYev : ∀ᶠ Y : ℕ in atTop, 1 / (Y : ℝ) < ε / 2 :=
    (tendsto_order.mp tendsto_one_div_atTop_nhds_zero_nat).2 (ε / 2) hε₂
  obtain ⟨Y, hY, hYε⟩ := ((eventually_gt_atTop (0 : ℕ)).and hYev).exists
  let S := Nat.primesLE Y
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := Nat.prime_of_mem_primesLE hp
  obtain ⟨L, hLε⟩ := ((tendsto_order.mp (tendsto_finitePrime_tail S hS)).2 (ε / 2) hε₂).exists
  refine ⟨rankinFiniteTruncation S L, _, hasNaturalDensity_rankinFiniteTruncation S L hS, ?_⟩
  intro N
  exact (abs_densityUpTo_rankin_sub_truncation_le Y L N hY).trans (by
    linarith only [hYε, hLε])

end GRHArticle.ProgressionFree
