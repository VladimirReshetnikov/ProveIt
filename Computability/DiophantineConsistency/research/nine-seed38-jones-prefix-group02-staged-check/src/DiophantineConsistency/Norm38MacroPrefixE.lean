import DiophantineConsistency.Norm38MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup02
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 ExecutableJones

theorem prefix_e {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d5.values a (Fin.last 4) =
      ∑ k ∈ codingStar 38 4,
        ((indexZ Norm38MacroLanguage.seed 0 : R) + (pCoefficient Norm38MacroLanguage.seed k : R)) *
          (base a ^ (5 : Nat)) ^ ((5 ^ 39 : Nat) - codingExpo 38 4 k) := by
  rw [d5, Norm38MacroCuts.snoc_last]
  change (∑ k ∈ codingStar 38 4,
      ((indexZ Norm38MacroLanguage.seed 0 : R) + (pCoefficient Norm38MacroLanguage.seed k : R)) *
        (d4.values a ((Fin.last 1).castSucc.castSucc)) ^ ((5 ^ 39 : Nat) - codingExpo 38 4 k)) = _
  rw [d4_B]

#print axioms prefix_e
end DiophantineConsistency.Norm38MacroPrefixGroup02
