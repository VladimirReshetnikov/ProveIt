import DiophantineConsistency.Norm38MacroPrefixCarryOthers

/-! Candidate B/b relationship in d10; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixBPower
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup03 Norm38MacroPrefixGroup06

theorem d10_B_eq_b_pow {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
      (d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (5 : Nat) := by
  rw [d10_B_carry, d10_b_carry, d9_B, d9_b]

#print axioms d10_B_eq_b_pow
end DiophantineConsistency.Norm38MacroPrefixBPower
