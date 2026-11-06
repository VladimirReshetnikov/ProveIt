import DiophantineConsistency.Norm38MacroRankCodeLink
import DiophantineConsistency.Norm38MacroPrefixBPower

/-! Candidate d11 rankCode composition; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroRankComposition
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroRankRaw
  Norm38MacroRankCodeLink Norm38MacroPrefixBPower ExecutableJones

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

#print axioms d11_rankCode
end DiophantineConsistency.Norm38MacroRankComposition
