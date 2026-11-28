import GRHArticle.SingularModuli.Prime59.DiscriminantCheck
import GRHArticle.SingularModuli.Prime59.InvariantCheck
import GRHArticle.SingularModuli.Prime59.InputBounds

namespace GRHArticle.SingularModuli.Prime59

open scoped PowerSeries

theorem invariant_valid :
    SeriesPrefix invariantPrecision invariant integralNormalizedJExpansion := by
  apply ModularInvariantPrefixCertificate.invariantPrefix_of_checked _ sigma3 discriminant
  · rw [sigma3_length]; decide
  · intro i hi
    exact getD_sigma3 i (Nat.lt_succ_of_lt hi)
  · apply ModularInvariantPrefixCertificate.discriminantPrefix_of_checked _ sigma3 sigma5
    · rw [sigma3_length]; decide
    · rw [sigma5_length]; decide
    · exact getD_sigma3
    · exact getD_sigma5
    · exact discriminantCheck
  · exact invariantCheck

theorem invariantNatural_valid :
    SeriesPrefix invariantPrecision (invariantNatural.map Int.ofNat) integralNormalizedJExpansion := by
  simpa only [invariantNatural_map] using invariant_valid

theorem shortInvariant_valid :
    SeriesPrefix diagonalPrecision shortInvariant integralNormalizedJExpansion := by
  intro i
  rw [shortInvariant, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt,
    ← List.getD_eq_getElem?_getD]
  exact invariant_valid ⟨i, i.isLt.trans_le (by decide)⟩

end GRHArticle.SingularModuli.Prime59
