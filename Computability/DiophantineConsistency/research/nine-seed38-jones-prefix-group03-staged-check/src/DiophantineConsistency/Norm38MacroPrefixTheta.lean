import DiophantineConsistency.Norm38MacroPrefixCarry03

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup03
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup02 ExecutableJones

theorem prefix_theta {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d9.values a (Fin.last 8) = base a ^ (5 : Nat) -
      ((2 : Int) : R) * (indexZ Norm38MacroLanguage.seed 0 : R) := by
  rw [d9, Norm38MacroCuts.snoc_last]
  change (d8.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) -
    ((2 : Int) : R) * (indexZ Norm38MacroLanguage.seed 0 : R) = _
  rw [d8_B]

#print axioms prefix_theta
end DiophantineConsistency.Norm38MacroPrefixGroup03
