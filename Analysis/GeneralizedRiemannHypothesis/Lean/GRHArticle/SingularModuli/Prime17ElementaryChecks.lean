import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# The elementary rows and the final diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem elementaryCheck0 : ElementaryCheck 0 := by decide +kernel

private theorem elementaryCheck1 : ElementaryCheck 1 := by decide +kernel

private theorem elementaryCheck2 : ElementaryCheck 2 := by decide +kernel

private theorem elementaryCheck3 : ElementaryCheck 3 := by decide +kernel

private theorem elementaryCheck4 : ElementaryCheck 4 := by decide +kernel

private theorem elementaryCheck5 : ElementaryCheck 5 := by decide +kernel

private theorem elementaryCheck6 : ElementaryCheck 6 := by decide +kernel

private theorem elementaryCheck7 : ElementaryCheck 7 := by decide +kernel

private theorem elementaryCheck8 : ElementaryCheck 8 := by decide +kernel

private theorem elementaryCheck9 : ElementaryCheck 9 := by decide +kernel

private theorem elementaryCheck10 : ElementaryCheck 10 := by decide +kernel

private theorem elementaryCheck11 : ElementaryCheck 11 := by decide +kernel

private theorem elementaryCheck12 : ElementaryCheck 12 := by decide +kernel

private theorem elementaryCheck13 : ElementaryCheck 13 := by decide +kernel

private theorem elementaryCheck14 : ElementaryCheck 14 := by decide +kernel

private theorem elementaryCheck15 : ElementaryCheck 15 := by decide +kernel

private theorem elementaryCheck16 : ElementaryCheck 16 := by decide +kernel

theorem elementary_checks : ∀ k < 17, ElementaryCheck k := by
  have h : ∀ i : Fin 17, ElementaryCheck (i : ℕ) := by
    intro i
    fin_cases i
    · exact elementaryCheck0
    · exact elementaryCheck1
    · exact elementaryCheck2
    · exact elementaryCheck3
    · exact elementaryCheck4
    · exact elementaryCheck5
    · exact elementaryCheck6
    · exact elementaryCheck7
    · exact elementaryCheck8
    · exact elementaryCheck9
    · exact elementaryCheck10
    · exact elementaryCheck11
    · exact elementaryCheck12
    · exact elementaryCheck13
    · exact elementaryCheck14
    · exact elementaryCheck15
    · exact elementaryCheck16
  exact fun k hk ↦ h ⟨k, hk⟩

theorem elementary_zero_check : ElementaryZeroCheck := by decide +kernel

theorem diagonal_check : DiagonalCheck := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
