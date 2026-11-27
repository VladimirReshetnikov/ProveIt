import GRHArticle.ProgressionFree.FinitePrimeBlockCountingApproximation
import GRHArticle.ProgressionFree.FiniteLengthProgressionTest

/-!
# A finite rational search over bounded prime blocks

Enumerate disjoint finite families of prime blocks in an initial segment,
and enumerate progression-free subsets of each bounded exponent box.
The local probabilities and the fixed exterior probabilities are
rational finite products and sums.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The possible exceptional block families inside the prime cutoff. -/
def finitePrimeBlockFamilyCandidates (d Z : ℕ) : Finset (Finset (Finset ℕ)) :=
  ((Nat.primesLE Z).powerset.powerset).filter (fun S ↦
    (∀ P ∈ S, P.Nonempty ∧ P.card ≤ d) ∧
      ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Disjoint P Q)

theorem mem_finitePrimeBlockFamilyCandidates {d Z : ℕ} {S : Finset (Finset ℕ)} :
    S ∈ finitePrimeBlockFamilyCandidates d Z ↔
      (∀ P ∈ S, P.Nonempty ∧ P ⊆ Nat.primesLE Z ∧ P.card ≤ d) ∧
      (S : Set (Finset ℕ)).PairwiseDisjoint id := by
  simp only [finitePrimeBlockFamilyCandidates,mem_filter,mem_powerset]
  constructor
  · rintro ⟨hsub,hcard,hpair⟩
    exact ⟨fun P hp ↦ ⟨(hcard P hp).1,mem_powerset.mp (hsub hp),(hcard P hp).2⟩,
      fun P hp Q hq hne ↦ hpair P hp Q hq hne⟩
  · rintro ⟨h,hpair⟩
    exact ⟨fun P hp ↦ mem_powerset.mpr (h P hp).2.1,
      fun P hp ↦ ⟨(h P hp).1,(h P hp).2.2⟩,fun P hp Q hq hne ↦ hpair hp hq hne⟩

private theorem familyCandidates_nonempty (d Z : ℕ) :
    (finitePrimeBlockFamilyCandidates d Z).Nonempty :=
  ⟨∅,by simp [finitePrimeBlockFamilyCandidates]⟩

/-- The computable box of all small exponent vectors on a block. -/
def finiteBlockExponentBox (P : Finset ℕ) (L : ℕ) : Finset (↥P → ℕ) :=
  Fintype.piFinset fun _ : ↥P ↦ range L

/-- The progression-free finite choices in a block exponent box. -/
def finiteExponentBlockCandidates (k : ℕ) (P : Finset ℕ) (L : ℕ) : Finset (Finset (↥P → ℕ)) :=
  (finiteBlockExponentBox P L).powerset.filter (fun A ↦ finiteLengthVectorAPTest k A = true)

private theorem exponentBlockCandidates_nonempty (k : ℕ) (P : Finset ℕ) (L : ℕ) :
    (finiteExponentBlockCandidates k P L).Nonempty :=
  ⟨∅,by simp [finiteExponentBlockCandidates,finiteLengthVectorAPTest]⟩

theorem mem_finiteExponentBlockCandidates {k : ℕ} (hk : 2 ≤ k) {P : Finset ℕ} {L : ℕ}
    {A : Finset (↥P → ℕ)} :
    A ∈ finiteExponentBlockCandidates k P L ↔
      A ⊆ finiteBlockExponentBox P L ∧ KTermVectorAPFree k (A : Set (↥P → ℕ)) := by
  simp only [finiteExponentBlockCandidates,mem_filter,mem_powerset,finiteLengthVectorAPTest_spec hk]

/-- Rational local probability of a finite block rule. -/
def finiteBlockProbabilityRat (P : Finset ℕ) (A : Finset (↥P → ℕ)) : ℚ :=
  (∏ p : ↥P, (1-1/(p.val : ℚ))) *
    ∑ v ∈ A, ∏ p : ↥P, (1/(p.val : ℚ))^v p

theorem cast_finiteBlockProbabilityRat (P : Finset ℕ) (A : Finset (↥P → ℕ)) :
    (finiteBlockProbabilityRat P A : ℝ) = primeBlockProbability P (A : Set (↥P → ℕ)) := by
  have hMass : reciprocalExponentMass (fun p : ↥P ↦ 1/(p.val:ℝ)) (A : Set (↥P → ℕ)) =
      ∑ v ∈ A, reciprocalExponentWeight (fun p : ↥P ↦ 1/(p.val:ℝ)) v :=
    (reciprocalExponentMass_eq_tsum_subtype _ _).trans (Finset.tsum_subtype A _)
  rw [primeBlockProbability,hMass]
  simp [finiteBlockProbabilityRat,reciprocalExponentWeight]

/-- The largest rational probability of a progression-free rule in the box. -/
def finiteExponentBlockOptimum (k : ℕ) (P : Finset ℕ) (L : ℕ) : ℚ :=
  (finiteExponentBlockCandidates k P L).sup' (exponentBlockCandidates_nonempty k P L)
    (finiteBlockProbabilityRat P)

private def finiteGreedyLengthExponents (k L : ℕ) : Finset ℕ :=
  (range L).filter fun j ↦ greedyLengthKeep k j = true

private theorem finiteGreedyLengthExponents_eq (k L : ℕ) :
    finiteGreedyLengthExponents k L = exponentsBelow (greedyLengthExponents k) L := by
  ext j
  simp only [finiteGreedyLengthExponents,exponentsBelow,mem_filter,greedyLengthExponents,Set.mem_setOf_eq]

/-- The score of a fixed family, after exact local optimization and
finite truncation of the independent exterior. -/
def finitePrimeBlockFamilyScore (k : ℕ) (S : Finset (Finset ℕ)) (U L : ℕ) : ℚ :=
  (∏ P ∈ S, finiteExponentBlockOptimum k P L) *
    ∏ p ∈ finiteBlockExteriorPrimes S U, (1-1/(p : ℚ)) *
      ∑ e ∈ finiteGreedyLengthExponents k L, (1/(p : ℚ))^e

private theorem cast_finitePrimeBlockFamilyScore (k : ℕ) (S : Finset (Finset ℕ)) (U L : ℕ) :
    (finitePrimeBlockFamilyScore k S U L : ℝ) =
      (∏ P ∈ S, (finiteExponentBlockOptimum k P L : ℝ)) *
        ∏ p ∈ finiteBlockExteriorPrimes S U, (1-1/(p : ℝ)) *
          ∑ e ∈ exponentsBelow (greedyLengthExponents k) L, (1/(p : ℝ))^e := by
  simp [finitePrimeBlockFamilyScore,finiteGreedyLengthExponents_eq]

/-- Exact finite optimization over all admitted block families. -/
def integerBoundedPrimeBlockDensityApproxAt (k d Z U L : ℕ) : ℚ :=
  (finitePrimeBlockFamilyCandidates d Z).sup' (familyCandidates_nonempty d Z)
    (fun S ↦ finitePrimeBlockFamilyScore k S U L)

private theorem approx_cap_mem {k : ℕ} (hk : 2 ≤ k) {P : Finset ℕ} {L : ℕ}
    {F : Set (↥P → ℕ)} (hF : KTermVectorAPFree k F) :
    blockPatternsBelow F L ∈ finiteExponentBlockCandidates k P L := by
  apply (mem_finiteExponentBlockCandidates hk).mpr
  refine ⟨fun v hv ↦ ?_,?_⟩
  · exact Fintype.mem_piFinset.mpr (fun p ↦ mem_range.mpr ((mem_blockPatternsBelow.mp hv).2 p))
  · intro v a d hv hAffine
    exact hF v a d (fun i ↦ (mem_blockPatternsBelow.mp (hv i)).1) hAffine

/-- Finite search dominates the finite approximation to any candidate
family and progression-free block rules. -/
theorem finiteExceptionPrimeRuleApproximationDensity_le_search {k d Z : ℕ} (hk : 2 ≤ k)
    {S : Finset (Finset ℕ)} (hS : S ∈ finitePrimeBlockFamilyCandidates d Z)
    (R : (P : Finset ℕ) → Set (↥P → ℕ)) (hR : ∀ P ∈ S, KTermVectorAPFree k (R P))
    (U L : ℕ) :
    finiteExceptionPrimeRuleApproximationDensity S R (greedyLengthExponents k) U L ≤
      (integerBoundedPrimeBlockDensityApproxAt k d Z U L : ℝ) := by
  have hMax := (Rat.cast_le (K := ℝ)).mpr
    (le_sup' (fun T ↦ finitePrimeBlockFamilyScore k T U L) hS)
  refine le_trans ?_ hMax
  rw [cast_finitePrimeBlockFamilyScore]
  unfold finiteExceptionPrimeRuleApproximationDensity
  apply mul_le_mul_of_nonneg_right
  · apply prod_le_prod
    · intro P hP
      exact primeBlockProbability_nonneg (fun p hp ↦
        Nat.prime_of_mem_primesLE (((mem_finitePrimeBlockFamilyCandidates.mp hS).1 P hP).2.1 hp)) _
    · intro P hP
      rw [← cast_finiteBlockProbabilityRat]
      exact (Rat.cast_le (K := ℝ)).mpr (le_sup' (finiteBlockProbabilityRat P)
        (approx_cap_mem hk (hR P hP)))
  · apply prod_nonneg
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1
    exact mul_nonneg (sub_nonneg.mpr
      ((div_le_one (by exact_mod_cast hprime.pos)).mpr (by exact_mod_cast hprime.one_lt.le)))
      (sum_nonneg fun e _ ↦ by positivity)

/-- Some finite family and explicit finite rules realize the search score. -/
theorem exists_finiteExceptionPrimeRuleApproximationDensity_eq_search {k : ℕ} (hk : 2 ≤ k)
    (d Z U L : ℕ) :
    ∃ (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ)),
      S ∈ finitePrimeBlockFamilyCandidates d Z ∧ (∀ P ∈ S, KTermVectorAPFree k (R P)) ∧
      finiteExceptionPrimeRuleApproximationDensity S R (greedyLengthExponents k) U L =
        (integerBoundedPrimeBlockDensityApproxAt k d Z U L : ℝ) := by
  classical
  obtain ⟨S,hS,hMax⟩ := exists_mem_eq_sup' (familyCandidates_nonempty d Z)
    (fun T ↦ finitePrimeBlockFamilyScore k T U L)
  change integerBoundedPrimeBlockDensityApproxAt k d Z U L = _ at hMax
  have hArg (P : Finset ℕ) : ∃ A ∈ finiteExponentBlockCandidates k P L,
      finiteExponentBlockOptimum k P L = finiteBlockProbabilityRat P A :=
    exists_mem_eq_sup' (exponentBlockCandidates_nonempty k P L) (finiteBlockProbabilityRat P)
  choose A hA heq using hArg
  let R (P : Finset ℕ) : Set (↥P → ℕ) := A P
  have hBox (P : Finset ℕ) : blockPatternsBelow (R P) L = A P := by
    ext v
    rw [mem_blockPatternsBelow]
    change (v ∈ A P ∧ ∀ p, v p < L) ↔ v ∈ A P
    refine ⟨And.left,fun hv ↦ ⟨hv,fun p ↦ ?_⟩⟩
    have hbox : v ∈ Fintype.piFinset (fun _ : ↥P ↦ range L) :=
      ((mem_finiteExponentBlockCandidates hk).mp (hA P)).1 hv
    exact mem_range.mp (Fintype.mem_piFinset.mp hbox p)
  refine ⟨S,R,hS,fun P _ ↦ ((mem_finiteExponentBlockCandidates hk).mp (hA P)).2,?_⟩
  rw [hMax,cast_finitePrimeBlockFamilyScore,finiteExceptionPrimeRuleApproximationDensity]
  congr 1
  apply prod_congr rfl
  intro P _
  rw [hBox P,heq P,cast_finiteBlockProbabilityRat]

end GRHArticle.ProgressionFree
