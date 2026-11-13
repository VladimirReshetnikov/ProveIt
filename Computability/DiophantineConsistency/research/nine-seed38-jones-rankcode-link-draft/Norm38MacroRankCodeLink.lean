import DiophantineConsistency.Norm38MacroRankCarry

/-! Candidate generic link; no full-recipe or JSON theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroRankCodeLink
open Norm38MacroRankRaw

theorem rankRaw_eq_rankCode {R : Type*} [CommRing R]
    (z b q n e ell lam g theta : R) :
    rankRaw z b (b ^ (5 : Nat)) q n e ell lam g theta =
      NinePolynomial.rankCode (1 : R) z b e g ell n q theta lam := by
  simp only [rankRaw, NinePolynomial.rankCode, one_mul]

#print axioms rankRaw_eq_rankCode
end DiophantineConsistency.Norm38MacroRankCodeLink
