import DiophantineConsistency.Norm38MacroPrefixGroup01

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup02
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 ExecutableJones

theorem d4_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d4.values a ((Fin.last 1).castSucc.castSucc) = base a ^ (5 : Nat) := by
  calc
    d4.values a ((Fin.last 1).castSucc.castSucc) =
        d3.values a ((Fin.last 1).castSucc) := by
      change (Dag.snoc d3 _).values a (Fin.castSucc ((Fin.last 1).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d3 _ ((Fin.last 1).castSucc)
    _ = d2.values a (Fin.last 1) := by
      change (Dag.snoc d2 _).values a (Fin.castSucc (Fin.last 1)) = _
      exact Norm38MacroCuts.snoc_previous a d2 _ (Fin.last 1)
    _ = base a ^ (5 : Nat) := prefix_B a

theorem d5_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d5.values a ((Fin.last 1).castSucc.castSucc.castSucc) = base a ^ (5 : Nat) := by
  change (Dag.snoc d4 _).values a (Fin.castSucc ((Fin.last 1).castSucc.castSucc)) = _
  exact (Norm38MacroCuts.snoc_previous a d4 _ ((Fin.last 1).castSucc.castSucc)).trans (d4_B a)

theorem d6_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d6.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc) = base a ^ (5 : Nat) := by
  change (Dag.snoc d5 _).values a (Fin.castSucc ((Fin.last 1).castSucc.castSucc.castSucc)) = _
  exact (Norm38MacroCuts.snoc_previous a d5 _ ((Fin.last 1).castSucc.castSucc.castSucc)).trans (d5_B a)

#print axioms d4_B
#print axioms d5_B
#print axioms d6_B
end DiophantineConsistency.Norm38MacroPrefixGroup02
