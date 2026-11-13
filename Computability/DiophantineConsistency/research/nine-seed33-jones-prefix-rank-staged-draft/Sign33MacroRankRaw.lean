import DiophantineConsistency.Sign33MacroPrefixCarrySums
import DiophantineConsistency.Sign33MacroPrefixCarryOthers

/-! Candidate symbolic d11 rank-node equation; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroRankRaw
open Sign33MacroLanguage Sign33MacroPrefixes ExecutableJones

def rankRaw {R : Type*} [CommRing R] (z b B q n e ell lam g theta : R) : R :=
  (g + e * q ^ 3 + ell * q ^ 5 +
    (2 * (e - z * lam) * (1 + B + g) ^ 4 + lam * B + lam * B * q ^ 4) * q ^ 7) *
      (n ^ 2 - n) +
    (q ^ 3 - b * ell + ell + theta * lam * q ^ 3 + (B - 2) * q ^ 8) * (n ^ 2 - 1)

theorem d11_rank_raw {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d11.values a (Fin.last 10) =
      rankRaw (indexZ seed 0 : R) (d10.values a ⟨0, by decide⟩)
        (d10.values a ⟨1, by decide⟩) (d10.values a ⟨2, by decide⟩)
        (d10.values a ⟨3, by decide⟩) (d10.values a ⟨4, by decide⟩)
        (d10.values a ⟨5, by decide⟩) (d10.values a ⟨6, by decide⟩)
        (d10.values a ⟨7, by decide⟩) (d10.values a ⟨8, by decide⟩) := by
  rw [d11, Sign33MacroCuts.snoc_last]
  simp only [Term.eval, NExpr.eval, rankRaw, Int.cast_one, Int.cast_ofNat]

#print axioms d11_rank_raw
end DiophantineConsistency.Sign33MacroRankRaw
