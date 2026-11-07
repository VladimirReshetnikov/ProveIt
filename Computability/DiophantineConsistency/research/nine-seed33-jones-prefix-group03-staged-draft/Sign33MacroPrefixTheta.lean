import DiophantineConsistency.Sign33MacroPrefixCarry03

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup03
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 Sign33MacroPrefixGroup02 ExecutableJones

theorem prefix_theta {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d9.values a (Fin.last 8) = base a ^ (5 : Nat) -
      ((2 : Int) : R) * (indexZ Sign33MacroLanguage.seed 0 : R) := by
  rw [d9, Sign33MacroCuts.snoc_last]
  change (d8.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) -
    ((2 : Int) : R) * (indexZ Sign33MacroLanguage.seed 0 : R) = _
  rw [d8_B]

#print axioms prefix_theta
end DiophantineConsistency.Sign33MacroPrefixGroup03
