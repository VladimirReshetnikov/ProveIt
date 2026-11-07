import DiophantineConsistency.Sign33MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup02
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 ExecutableJones

theorem prefix_ell {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d6.values a (Fin.last 5) =
      ∑ j ∈ Finset.range 33, (base a ^ (5 : Nat)) ^ (5 ^ (j + 1)) := by
  rw [d6, Sign33MacroCuts.snoc_last]
  change (∑ j ∈ Finset.range 33,
      (d5.values a ((Fin.last 1).castSucc.castSucc.castSucc)) ^ (5 ^ (j + 1))) = _
  rw [d5_B]

#print axioms prefix_ell
end DiophantineConsistency.Sign33MacroPrefixGroup02
