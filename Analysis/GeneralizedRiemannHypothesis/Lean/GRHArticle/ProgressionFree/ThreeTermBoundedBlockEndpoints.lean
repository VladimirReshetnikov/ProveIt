import GRHArticle.ProgressionFree.BoundedPrimeBlockWidth225
import GRHArticle.ProgressionFree.GreedyLengthThree
import GRHArticle.ProgressionFree.SingletonPrimeBlocks

/-!
# Rankin density at the three-term width endpoints

The width-one optimum is the Rankin density. The verified width-225
exchange gives an upper bound on the first improving width.
-/

namespace GRHArticle.ProgressionFree

/-- The singleton optimum for three-term progressions is exactly Rankin's
natural density. -/
theorem integerBoundedPrimeBlockDensitySupremum_three_one_eq_rankin :
    integerBoundedPrimeBlockDensitySupremum 3 1 = integerUpperDensity rankinSet := by
  obtain ⟨e,he⟩ := exists_hasNaturalDensity_integerGreedyLengthSet (by decide : 3 ≤ 3)
  have hOne := integerBoundedPrimeBlockDensitySupremum_one_eq_greedy (by decide : 3 ≤ 3) he
  rw [integerGreedyLengthSet_three_eq_rankinSet] at he
  exact hOne.trans (integerUpperDensity_eq_of_hasNaturalDensity he).symm

/-- There is a least positive width improving on Rankin, and it is at most
225. The singleton theorem excludes width one. -/
theorem exists_least_improving_primeBlockWidth_three :
    ∃ d : ℕ, 2 ≤ d ∧ d ≤ 225 ∧
      integerUpperDensity rankinSet < integerBoundedPrimeBlockDensitySupremum 3 d ∧
      ∀ m : ℕ, 0 < m → m < d →
        integerBoundedPrimeBlockDensitySupremum 3 m ≤ integerUpperDensity rankinSet := by
  classical
  let P (d : ℕ) := 0 < d ∧ integerUpperDensity rankinSet < integerBoundedPrimeBlockDensitySupremum 3 d
  have hPos : (0 : ℝ) < 1/10^596 := by positivity
  have h225 : P 225 := ⟨by decide,sub_pos.mp (hPos.trans one_div_ten_pow_lt_width225_sub_rankin)⟩
  have hE : ∃ d, P d := ⟨225,h225⟩
  obtain ⟨hd,hGain⟩ := Nat.find_spec hE
  have hNe : Nat.find hE ≠ 1 := by
    intro he
    rw [he,integerBoundedPrimeBlockDensitySupremum_three_one_eq_rankin] at hGain
    exact (lt_irrefl _) hGain
  refine ⟨Nat.find hE,by omega,Nat.find_min' hE h225,hGain,?_⟩
  intro m hm hmd
  apply le_of_not_gt
  exact fun h ↦ Nat.find_min hE hmd ⟨hm,h⟩

end GRHArticle.ProgressionFree
