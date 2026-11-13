import DiophantineConsistency.Sign33MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup02
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 ExecutableJones

theorem prefix_lambda {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d7.values a (Fin.last 6) =
      ∑ j ∈ Finset.range (4 * (5 ^ 34 : Nat)), (base a ^ (5 : Nat)) ^ j := by
  rw [d7, Sign33MacroCuts.snoc_last]
  change (∑ j ∈ Finset.range (4 * (5 ^ 34 : Nat)),
      (d6.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc)) ^ j) = _
  rw [d6_B]

#print axioms prefix_lambda
end DiophantineConsistency.Sign33MacroPrefixGroup02
