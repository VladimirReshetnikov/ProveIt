import GRHArticle.ProgressionFree.ImprovingPrimeBlocks
import GRHArticle.ProgressionFree.SingletonPrimeBlocks

/-!
# Every fixed finite prime-block width loses density

A width bound limits the exceptional support of a reduced competitor.
A finite family of disjoint improving exchanges gives a common positive
multiplicative gain for all such competitors.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped BigOperators

private theorem le_lengthNaturalDensitySupremum {k : ℕ} {A : Set ℕ} {e : ℝ}
    (h0 : 0 ∉ A) (hF : KTermGPFree k A) (hD : HasNaturalDensity A e) :
    e ≤ integerLengthNaturalDensitySupremum k := by
  unfold integerLengthNaturalDensitySupremum
  exact le_csSup ⟨1,by rintro x ⟨B,_,_,hB⟩; exact naturalDensity_le_one hB⟩ ⟨A,h0,hF,hD⟩

/-- A strictly positive density gap for every length and every finite
positive block width. This proves the strict inequality of
`gpi:thm:blocksk` without first requiring an attained bounded optimum. -/
theorem integerBoundedPrimeBlockDensitySupremum_lt_lengthNaturalDensitySupremum
    {k d : ℕ} (hk : 3 ≤ k) (hd : 0 < d) :
    integerBoundedPrimeBlockDensitySupremum k d < integerLengthNaturalDensitySupremum k := by
  classical
  obtain ⟨dG,hG⟩ := exists_hasNaturalDensity_integerGreedyLengthSet hk
  have hGpos := (exists_improvingPrimeBlock_avoiding hk hG ∅).1
  have hGfree := kTermGPFree_integerGreedyLengthSet (by omega : 2 ≤ k)
  have hGzero : 0 ∉ integerGreedyLengthSet k := fun h ↦ h.1 rfl
  have hGsub := le_lengthNaturalDensitySupremum hGzero hGfree hG
  have hGwidth : IntegerBoundedPrimeBlockSet d (integerGreedyLengthSet k) := by
    obtain ⟨π,R,hW,he⟩ := integerBoundedPrimeBlockSet_greedyLength k
    exact ⟨π,R,fun P hP ↦ (hW P hP).trans hd,he⟩
  let S := {a | ∃ A, IntegerBoundedPrimeBlockSet d A ∧ KTermGPFree k A ∧ a = integerUpperDensity A}
  have hGmem : dG ∈ S := ⟨integerGreedyLengthSet k,hGwidth,hGfree,
    (integerUpperDensity_eq_of_hasNaturalDensity hG).symm⟩
  have hSbdd : BddAbove S := ⟨1,by rintro x ⟨A,_,_,rfl⟩; exact integerUpperDensity_le_one A⟩
  have hSupPos : 0 < sSup S := hGpos.trans_le (le_csSup hSbdd hGmem)
  let n := d*(Nat.primesLE (2*d)).card
  obtain ⟨E,hPair⟩ := exists_disjoint_improvingPrimeBlocks hk hG (n+1)
  let old (i : Fin (n+1)) := primeBlockProbability (E i).primes (greedyExponentPatterns _ k)
  let new (i : Fin (n+1)) := primeBlockProbability (E i).primes (E i).rule
  have hOld (i : Fin (n+1)) : 0 < old i :=
    primeBlockProbability_greedy_pos (by omega : 2 ≤ k) (E i).primeOfMem
  let ratio (i : Fin (n+1)) := new i / old i - 1
  have hRatio (i : Fin (n+1)) : 0 < ratio i := by
    dsimp only [ratio]
    apply sub_pos.mpr
    exact (lt_div_iff₀ (hOld i)).mpr (by simpa only [one_mul] using (E i).gain)
  obtain ⟨i,_,hMin⟩ := exists_min_image (univ : Finset (Fin (n+1))) ratio univ_nonempty
  let δ := ratio i
  have hδ : 0 < δ := hRatio i
  have hFactor (j : Fin (n+1)) : old j * (1+δ) ≤ new j := by
    have h := hMin j (mem_univ _)
    have he : 1+δ ≤ new j / old j := by dsimp only [δ,ratio] at h ⊢; linarith
    simpa only [mul_comm] using (le_div_iff₀ (hOld j)).mp he
  have hPos : 0 < 1+δ := by linarith
  have hbound : sSup S ≤ integerLengthNaturalDensitySupremum k / (1+δ) := by
    apply csSup_le ⟨dG,hGmem⟩
    rintro y ⟨A,⟨π,R,hwidth,rfl⟩,hFree,rfl⟩
    apply (le_div_iff₀ hPos).2
    by_cases hA : (integerPrimePartitionRule π R).Nonempty
    · obtain ⟨H,e,hH,hRule,hcard,he,hU⟩ :=
        exists_dominating_finiteExceptionPrimeRule hk hd π R hwidth hA hFree
      obtain ⟨j,hj⟩ := exists_improvingPrimeBlock_disjoint_of_card_le hPair hcard
      have hpr (P : Finset ℕ) (hP : P ∈ H) := π.primes P (hH P hP)
      have hpair : (H : Set (Finset ℕ)).PairwiseDisjoint id :=
        fun P hP Q hQ hneq ↦ π.pairwiseDisjoint (hH P hP) (hH Q hQ) hneq
      obtain ⟨A',a',hA'₀,hA'free,hA'd,hEq⟩ :=
        exists_density_of_disjoint_primeBlock_upgrade hk R hpr hpair hRule
          (E j).primeOfMem (E j).nonempty hj (E j).rule (E j).free he hG
      have he₀ : 0 ≤ e := ge_of_tendsto' he (densityUpTo_nonneg _)
      have hGain : e*(1+δ) ≤ a' := (mul_le_mul_iff_of_pos_right (hOld j)).1 (calc
        _ = e*(old j*(1+δ)) := by ring
        _ ≤ e*new j := mul_le_mul_of_nonneg_left (hFactor j) he₀
        _ = _ := hEq.symm)
      exact (mul_le_mul_of_nonneg_right hU hPos.le).trans
        (hGain.trans (le_lengthNaturalDensitySupremum hA'₀ hA'free hA'd))
    · rw [Set.not_nonempty_iff_eq_empty.mp hA,integerUpperDensity_eq_of_hasNaturalDensity hasNaturalDensity_empty,
        zero_mul]
      exact hGpos.le.trans hGsub
  have hstrict : sSup S < sSup S*(1+δ) := by
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left (show (1 : ℝ) < 1+δ by linarith) hSupPos
  exact hstrict.trans_le ((le_div_iff₀ hPos).mp hbound)

end GRHArticle.ProgressionFree
