import DiophantineConsistency.Norm38MacroPrefixCarry03

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup03
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup02 ExecutableJones

theorem prefix_G {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a (Fin.last 9) = ((32 : Int) : R) * base a *
      (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat) := by
  rw [d10, Norm38MacroCuts.snoc_last]
  change ((32 : Int) : R) *
    (d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) *
    (d9.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (5 ^ 38 : Nat) = _
  rw [d9_b, d9_B]

#print axioms prefix_G
end DiophantineConsistency.Norm38MacroPrefixGroup03
