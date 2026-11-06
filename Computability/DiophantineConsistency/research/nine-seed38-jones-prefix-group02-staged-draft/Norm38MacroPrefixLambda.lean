import DiophantineConsistency.Norm38MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup02
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 ExecutableJones

theorem prefix_lambda {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d7.values a (Fin.last 6) =
      ∑ j ∈ Finset.range (4 * (5 ^ 39 : Nat)), (base a ^ (5 : Nat)) ^ j := by
  rw [d7, Norm38MacroCuts.snoc_last]
  change (∑ j ∈ Finset.range (4 * (5 ^ 39 : Nat)),
      (d6.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc)) ^ j) = _
  rw [d6_B]

#print axioms prefix_lambda
end DiophantineConsistency.Norm38MacroPrefixGroup02
