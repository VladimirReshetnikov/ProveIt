import DiophantineConsistency.Sign33MacroPrefixCarry03

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup03
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 Sign33MacroPrefixGroup02 ExecutableJones

theorem prefix_G {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a (Fin.last 9) = ((32 : Int) : R) * base a *
      (base a ^ (5 : Nat)) ^ (5 ^ 33 : Nat) := by
  rw [d10, Sign33MacroCuts.snoc_last]
  change ((32 : Int) : R) *
    (d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) *
    (d9.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (5 ^ 33 : Nat) = _
  rw [d9_b, d9_B]

#print axioms prefix_G
end DiophantineConsistency.Sign33MacroPrefixGroup03
