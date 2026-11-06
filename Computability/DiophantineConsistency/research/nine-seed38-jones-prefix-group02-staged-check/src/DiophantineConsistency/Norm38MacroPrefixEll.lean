import DiophantineConsistency.Norm38MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup02
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 ExecutableJones

theorem prefix_ell {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d6.values a (Fin.last 5) =
      ∑ j ∈ Finset.range 38, (base a ^ (5 : Nat)) ^ (5 ^ (j + 1)) := by
  rw [d6, Norm38MacroCuts.snoc_last]
  change (∑ j ∈ Finset.range 38,
      (d5.values a ((Fin.last 1).castSucc.castSucc.castSucc)) ^ (5 ^ (j + 1))) = _
  rw [d5_B]

#print axioms prefix_ell
end DiophantineConsistency.Norm38MacroPrefixGroup02
