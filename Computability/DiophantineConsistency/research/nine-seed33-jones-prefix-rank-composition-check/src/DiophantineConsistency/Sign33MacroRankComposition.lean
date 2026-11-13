import DiophantineConsistency.Sign33MacroRankCodeLink
import DiophantineConsistency.Sign33MacroPrefixBPower

/-! Candidate d11 rankCode composition; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroRankComposition
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroRankRaw
  Sign33MacroRankCodeLink Sign33MacroPrefixBPower ExecutableJones

theorem d11_rankCode {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d11.values a (Fin.last 10) =
      NinePolynomial.rankCode (1 : R) (indexZ seed 0 : R)
        (d10.values a ⟨0, by decide⟩) (d10.values a ⟨4, by decide⟩)
        (d10.values a ⟨7, by decide⟩) (d10.values a ⟨5, by decide⟩)
        (d10.values a ⟨3, by decide⟩) (d10.values a ⟨2, by decide⟩)
        (d10.values a ⟨8, by decide⟩) (d10.values a ⟨6, by decide⟩) := by
  rw [d11_rank_raw]
  change rankRaw (indexZ seed 0 : R)
        (d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ⟨2, by decide⟩) (d10.values a ⟨3, by decide⟩)
        (d10.values a ⟨4, by decide⟩) (d10.values a ⟨5, by decide⟩)
        (d10.values a ⟨6, by decide⟩) (d10.values a ⟨7, by decide⟩)
        (d10.values a ⟨8, by decide⟩) = _
  rw [d10_B_eq_b_pow, rankRaw_eq_rankCode]
  have h : ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : Fin 10) = ⟨0, by decide⟩ := by decide
  rw [h]

#print axioms d11_rankCode
end DiophantineConsistency.Sign33MacroRankComposition
