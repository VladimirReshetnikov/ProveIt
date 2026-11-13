import DiophantineConsistency.Sign33MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup02
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 ExecutableJones

theorem prefix_e {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d5.values a (Fin.last 4) =
      ∑ k ∈ codingStar 33 4,
        ((indexZ Sign33MacroLanguage.seed 0 : R) + (pCoefficient Sign33MacroLanguage.seed k : R)) *
          (base a ^ (5 : Nat)) ^ ((5 ^ 34 : Nat) - codingExpo 33 4 k) := by
  rw [d5, Sign33MacroCuts.snoc_last]
  change (∑ k ∈ codingStar 33 4,
      ((indexZ Sign33MacroLanguage.seed 0 : R) + (pCoefficient Sign33MacroLanguage.seed k : R)) *
        (d4.values a ((Fin.last 1).castSucc.castSucc)) ^ ((5 ^ 34 : Nat) - codingExpo 33 4 k)) = _
  rw [d4_B]

#print axioms prefix_e
end DiophantineConsistency.Sign33MacroPrefixGroup02
