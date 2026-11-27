import GRHArticle.ProgressionFree.BoundedPrimeBlockFiniteSearch
import GRHArticle.ProgressionFree.FiniteExceptionPrimeBlockTruncation
import GRHArticle.ProgressionFree.PrimeBlockReduction
import GRHArticle.ProgressionFree.SingletonPrimeBlocks
import GRHArticle.ProgressionFree.WidthPreservingFiniteExceptions

/-!
# Uniform computation of the bounded prime-block supremum

There are only finitely many exceptional primes in a dominating rule.
Pruning large exceptional primes, bounding local exponents, and ignoring
large exterior primes each has an explicit density error. A rational
finite search covers all rules remaining after these operations.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped BigOperators

/-- Error bounds for unrestricted numerical cutoffs. -/
theorem integerBoundedPrimeBlockDensityApproxAt_bounds {k d Z U : ℕ}
    (hk : 3 ≤ k) (hd : 0 < d) (hZ : 0 < Z) (hZU : Z ≤ U) (L : ℕ) :
    let a : ℝ := integerBoundedPrimeBlockDensityApproxAt k d Z U L
    let E : ℝ := 1/(U : ℝ) + ∑ p ∈ Nat.primesLE U, 1/(p : ℝ)^L
    a-E ≤ integerBoundedPrimeBlockDensitySupremum k d ∧
      integerBoundedPrimeBlockDensitySupremum k d ≤
        a + (d*(Nat.primesLE (2*d)).card : ℕ)/(Z : ℝ) + E := by
  classical
  let a : ℝ := integerBoundedPrimeBlockDensityApproxAt k d Z U L
  let E : ℝ := 1/(U : ℝ) + ∑ p ∈ Nat.primesLE U, 1/(p : ℝ)^L
  let h := d*(Nat.primesLE (2*d)).card
  let G := greedyLengthExponents k
  let D : Set ℝ := {u | ∃ A, IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧ u=integerUpperDensity A}
  have hD : BddAbove D := ⟨1,by rintro _ ⟨A,_,_,rfl⟩; exact integerUpperDensity_le_one A⟩
  have hD₀ : D.Nonempty := by
    obtain ⟨π,R,hW,heq⟩ := integerBoundedPrimeBlockSet_greedyLength k
    exact ⟨_,integerGreedyLengthSet k,⟨π,R,fun P hP ↦ (hW P hP).trans hd,heq⟩,
      kTermGPFree_integerGreedyLengthSet (by omega),rfl⟩
  have hG₀ : 0 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hG₁ : 1 ∈ G := mem_greedyLengthExponents_of_lt (by omega) (by omega)
  have hU : 0 < U := hZ.trans_le hZU
  have hPrimes : Nat.primesLE Z ⊆ Nat.primesLE U := by
    intro p hp
    obtain ⟨hpZ,hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpZ.trans hZU,hp⟩
  obtain ⟨S,R,hS,hFree,hScore⟩ :=
    exists_finiteExceptionPrimeRuleApproximationDensity_eq_search (by omega : 2 ≤ k) d Z U L
  obtain ⟨hSS,hSP⟩ := mem_finitePrimeBlockFamilyCandidates.mp hS
  have hpr (P : Finset ℕ) (hP : P ∈ S) : ∀ p ∈ P, p.Prime :=
    fun p hp ↦ Nat.prime_of_mem_primesLE ((hSS P hP).2.1 hp)
  have hCover (P : Finset ℕ) (hP : P ∈ S) : P ⊆ Nat.primesLE U :=
    ((hSS P hP).2.1).trans hPrimes
  obtain ⟨e,he⟩ := exists_hasNaturalDensity_finiteExceptionPrimeRule S R hG₀ hG₁ hpr hSP
  have hA := integerBoundedPrimeBlockSet_finiteExceptionPrimeRule hd S R G
    (fun P hP ↦ (hSS P hP).1) hpr hSP (fun P hP ↦ (hSS P hP).2.2)
  have hAF := kTermGPFree_finiteExceptionPrimeRule (by omega : 2 ≤ k) S R hFree
    (kTermAPFree_greedyLengthExponents (by omega))
  have heD : e ∈ D := ⟨finiteExceptionPrimeRule S R G,hA,hAF,
    (integerUpperDensity_eq_of_hasNaturalDensity he).symm⟩
  have hScoreErr := finiteExceptionPrimeRuleApproximationDensity_error hG₀ hG₁ S R U L hU hCover hSP he
  rw [hScore] at hScoreErr
  have hApproxNonneg : 0 ≤ a := by
    have hc := hasNaturalDensity_finiteExceptionPrimeRuleApproximation S R G U L hpr hSP
    rw [hScore] at hc
    exact ge_of_tendsto' hc (densityUpTo_nonneg _)
  change a-E ≤ sSup D ∧ sSup D ≤ a+(h:ℝ)/(Z:ℝ)+E
  constructor
  · exact (by linarith only [(abs_le.mp hScoreErr).1] : a-E ≤ e).trans (le_csSup hD heD)
  · apply csSup_le hD₀
    rintro u ⟨A,⟨π,rules,hWidth,rfl⟩,hAFree,rfl⟩
    by_cases hNon : (integerPrimePartitionRule π rules).Nonempty
    · obtain ⟨H,f,hH,hFreeH,hcard,hf,hA⟩ :=
        exists_dominating_finiteExceptionPrimeRule hk hd π rules hWidth hNon hAFree
      have hPairH : (H : Set (Finset ℕ)).PairwiseDisjoint id := fun P hP Q hQ hne ↦
        π.pairwiseDisjoint (hH P hP) (hH Q hQ) hne
      obtain ⟨T,R',g,hT,hTP,hg,hLoss⟩ := exists_small_finiteExceptionPrimeRule_of_density hZ H rules
        (fun P hP ↦ π.primes P (hH P hP)) hPairH (fun P hP ↦ hWidth P (hH P hP))
        hFreeH hG₀ hG₁ hf
      have hTC : T ∈ finitePrimeBlockFamilyCandidates d Z :=
        mem_finitePrimeBlockFamilyCandidates.mpr
          ⟨fun P hP ↦ ⟨(hT P hP).1,(hT P hP).2.1,(hT P hP).2.2.1⟩,hTP⟩
      have hSearch := finiteExceptionPrimeRuleApproximationDensity_le_search
        (by omega : 2 ≤ k) hTC R' (fun P hP ↦ (hT P hP).2.2.2) U L
      have hErr := finiteExceptionPrimeRuleApproximationDensity_error hG₀ hG₁ T R' U L hU
        (fun P hP ↦ ((hT P hP).2.1).trans hPrimes) hTP hg
      have hZr : (0 : ℝ) ≤ Z := by positivity
      have hRatio : ((H.biUnion id).card : ℝ)/(Z : ℝ) ≤ (h : ℝ)/(Z : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) hZr
      change integerUpperDensity (integerPrimePartitionRule π rules) ≤ a+(h:ℝ)/(Z:ℝ)+E
      linarith only [hA,hLoss,hRatio,hSearch,(abs_le.mp hErr).2]
    · rw [Set.not_nonempty_iff_eq_empty.mp hNon,integerUpperDensity_eq_of_hasNaturalDensity hasNaturalDensity_empty]
      have hE : 0 ≤ E := by dsimp [E]; positivity
      linarith [hApproxNonneg,hE,show (0:ℝ) ≤ (h:ℝ)/(Z:ℝ) by positivity]

private def blockApproximationScale (precision : ℕ) : ℕ := 2^(precision+3)

private def blockApproximationCutoff (d precision : ℕ) : ℕ :=
  max 2 ((d*(Nat.primesLE (2*d)).card)*blockApproximationScale precision)

private def blockApproximationExteriorCutoff (d precision : ℕ) : ℕ :=
  max (blockApproximationCutoff d precision) (blockApproximationScale precision)

/-- Uniform executable rational approximation to the width-`d` optimum. -/
def integerBoundedPrimeBlockDensityApprox (k d precision : ℕ) : ℚ :=
  let Z := blockApproximationCutoff d precision
  let U := blockApproximationExteriorCutoff d precision
  integerBoundedPrimeBlockDensityApproxAt k d Z U (U+precision+3)

/-- For each precision, the certified error is at most `2^(-(precision+1))`,
uniformly over progression lengths and positive width bounds. -/
theorem integerBoundedPrimeBlockDensityApprox_error {k d : ℕ}
    (hk : 3 ≤ k) (hd : 0 < d) (precision : ℕ) :
    |(integerBoundedPrimeBlockDensityApprox k d precision : ℝ) -
      integerBoundedPrimeBlockDensitySupremum k d| ≤ (1/2:ℝ)^(precision+1) := by
  let B := blockApproximationScale precision
  let Z := blockApproximationCutoff d precision
  let U := blockApproximationExteriorCutoff d precision
  let L := U+precision+3
  let h := d*(Nat.primesLE (2*d)).card
  have hBZ : h*B ≤ Z := le_max_right 2 _
  have hZU : Z ≤ U := le_max_left _ _
  have hBU : B ≤ U := le_max_right _ _
  have hZ₀ : 0 < Z := lt_of_lt_of_le (by decide : 0 < (2:ℕ)) (le_max_left _ _)
  have hB₀ : (0 : ℝ) < B := by dsimp [B,blockApproximationScale]; positivity
  have hZr : (0 : ℝ) < Z := by exact_mod_cast hZ₀
  have hUr : (0 : ℝ) < U := by exact_mod_cast hZ₀.trans_le hZU
  have hSmall : (h:ℝ)/(Z:ℝ) ≤ 1/(B:ℝ) :=
    (div_le_div_iff₀ hZr hB₀).mpr (by rw [one_mul]; exact_mod_cast hBZ)
  have hExterior : 1/(U:ℝ) ≤ 1/(B:ℝ) :=
    one_div_le_one_div_of_le hB₀ (by exact_mod_cast hBU)
  have hSq : (∑ p ∈ Nat.primesLE U, 1/(p:ℝ)^L) ≤ 1/(B:ℝ) := by
    have hcard : (Nat.primesLE U).card ≤ U+1 := by
      rw [← card_range (U+1)]
      exact card_le_card fun p hp ↦ mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1)
    have hcard' : ((Nat.primesLE U).card:ℝ) ≤ (2:ℝ)^U := by
      exact_mod_cast hcard.trans (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := U)))
    calc
      _ ≤ ∑ _ ∈ Nat.primesLE U, 1/(2:ℝ)^L := sum_le_sum fun p hp ↦
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num)
          (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) L)
      _ = ((Nat.primesLE U).card:ℝ)/(2:ℝ)^L := by rw [sum_const,nsmul_eq_mul,mul_one_div]
      _ ≤ (2:ℝ)^U/(2:ℝ)^L := div_le_div_of_nonneg_right hcard' (by positivity)
      _ = 1/(B:ℝ) := by
        dsimp [B,blockApproximationScale]
        rw [show L = U+(precision+3) by dsimp [L]; omega,pow_add]
        push_cast
        field_simp
  have hScale : 3*(1/(B:ℝ)) ≤ (1/2:ℝ)^(precision+1) := by
    have he : 1/(B:ℝ) = (1/2:ℝ)^(precision+3) := by simp [B,blockApproximationScale]
    rw [he,show precision+3 = precision+1+2 by omega,pow_add]
    norm_num
    nlinarith [show 0 ≤ (1/2:ℝ)^(precision+1) by positivity]
  obtain ⟨hL,hR⟩ := integerBoundedPrimeBlockDensityApproxAt_bounds hk hd hZ₀ hZU L
  change |(integerBoundedPrimeBlockDensityApproxAt k d Z U L:ℝ) -
    integerBoundedPrimeBlockDensitySupremum k d| ≤ _
  apply abs_le.mpr
  constructor
  · linarith only [hR,hSmall,hExterior,hSq,hScale]
  · linarith only [hL,hExterior,hSq,hScale,show 0 ≤ 1/(B:ℝ) by positivity]

end GRHArticle.ProgressionFree
