import GRHArticle.ProgressionFree.PrimeBlockSlotPacking
import GRHArticle.ProgressionFree.PrimeBlockReduction
import GRHArticle.ProgressionFree.SingletonPrimeBlocks

/-!
# Attainment of the bounded prime-block extremum

Heavy-block reduction bounds the number of exceptional rows uniformly.
The compact slot maximum is realized by an actual set with the greedy
rule at every prime outside finitely many exceptional blocks.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- For length at least three, the bounded-block upper-density supremum is
attained as a natural density with a greedy singleton rule off finitely
many exceptional prime blocks. -/
theorem exists_hasNaturalDensity_integerBoundedPrimeBlockDensitySupremum
    {k d : ℕ} (hk : 3 ≤ k) (hd : 0 < d) :
    ∃ (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ)),
      let A := finiteExceptionPrimeRule S R (greedyLengthExponents k)
      IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧
        HasNaturalDensity A (integerBoundedPrimeBlockDensitySupremum k d) := by
  obtain ⟨dG,hG⟩ := exists_hasNaturalDensity_integerGreedyLengthSet hk
  have hG₀ : 0 ≤ dG := ge_of_tendsto' hG (densityUpTo_nonneg _)
  let m := d*(Nat.primesLE (2*d)).card
  obtain ⟨x,hx,_,hMax⟩ := exists_maximal_primeBlockSlotScore (by omega : 2 ≤ k) m d
  obtain ⟨S,R,e,hWidth,hFree,hD,hScore⟩ := exists_primeBlockRule_realizing_slotScore hk hd hx hG₀ hG
  let A := finiteExceptionPrimeRule S R (greedyLengthExponents k)
  let D := {a | ∃ B, IntegerBoundedPrimeBlockSet d B ∧ KTermGPFree k B ∧ a = integerUpperDensity B}
  have hDmem : e ∈ D := ⟨A,hWidth,hFree,(integerUpperDensity_eq_of_hasNaturalDensity hD).symm⟩
  have hDbdd : BddAbove D := ⟨1,by rintro a ⟨B,_,_,rfl⟩; exact integerUpperDensity_le_one B⟩
  have he₀ : 0 ≤ e := ge_of_tendsto' hD (densityUpTo_nonneg _)
  have hLe : sSup D ≤ e := by
    apply csSup_le ⟨e,hDmem⟩
    rintro a ⟨B,⟨π,rules,hW,rfl⟩,hF,rfl⟩
    by_cases hB : (integerPrimePartitionRule π rules).Nonempty
    · obtain ⟨T,b,hT,hTF,hSupp,hb,hU⟩ :=
        exists_dominating_finiteExceptionPrimeRule hk hd π rules hW hB hF
      have hTp (P : Finset ℕ) (hP : P ∈ T) := π.primes P (hT P hP)
      have hPair : (T : Set (Finset ℕ)).PairwiseDisjoint id :=
        fun P hP Q hQ hneq ↦ π.pairwiseDisjoint (hT P hP) (hT Q hQ) hneq
      have hCard : T.card ≤ m := calc
        T.card = ∑ P ∈ T, (1 : ℕ) := by simp
        _ ≤ ∑ P ∈ T, P.card :=
          sum_le_sum fun P hP ↦ Finset.card_pos.mpr (π.nonempty P (hT P hP))
        _ = (T.biUnion id).card := (card_biUnion hPair).symm
        _ ≤ m := hSupp
      obtain ⟨y,hy,hRep⟩ := exists_primeBlockSlotScore_eq_prod (by omega : 2 ≤ k)
        T rules hCard (fun P hP ↦ hW P (hT P hP)) hTp hPair hTF
      calc
        _ ≤ b := hU
        _ = dG * ∏ P ∈ T, primeBlockRuleRatio k P (rules P) :=
          finiteExceptionPrimeRule_density_eq_greedy_mul hk rules hTp hPair hb hG
        _ = dG * primeBlockSlotScore k y := by rw [hRep]
        _ ≤ dG * primeBlockSlotScore k x := mul_le_mul_of_nonneg_left (hMax y hy) hG₀
        _ ≤ e := hScore
    · rw [Set.not_nonempty_iff_eq_empty.mp hB,integerUpperDensity_eq_of_hasNaturalDensity hasNaturalDensity_empty]
      exact he₀
  have hEq : integerBoundedPrimeBlockDensitySupremum k d = e := hLe.antisymm (le_csSup hDbdd hDmem)
  exact ⟨S,R,hWidth,hFree,hEq.symm ▸ hD⟩

end GRHArticle.ProgressionFree
