import DiophantineConsistency.Norm38MacroPrefixCarry

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup03
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup02 ExecutableJones

theorem d8_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d8.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = base a ^ (5 : Nat) := by
  calc
    d8.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d7.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d7 _ ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d6.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ((Fin.last 1).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d6 _ ((Fin.last 1).castSucc.castSucc.castSucc.castSucc)
    _ = base a ^ (5 : Nat) := d6_B a

theorem d9_B {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d9.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = base a ^ (5 : Nat) := by
  change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
  exact (Norm38MacroCuts.snoc_previous a d8 _ ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)).trans (d8_B a)

theorem d9_b {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = base a := by
  calc
    d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d8.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d8 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d7.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d7 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d6.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d6 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d5.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d5 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d5 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc)
    _ = d4.values a ((Fin.last 0).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d4 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d4 _ ((Fin.last 0).castSucc.castSucc.castSucc)
    _ = d3.values a ((Fin.last 0).castSucc.castSucc) := by
      change (Dag.snoc d3 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d3 _ ((Fin.last 0).castSucc.castSucc)
    _ = d2.values a ((Fin.last 0).castSucc) := by
      change (Dag.snoc d2 _).values a (Fin.castSucc ((Fin.last 0).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d2 _ ((Fin.last 0).castSucc)
    _ = d1.values a (Fin.last 0) := by
      change (Dag.snoc d1 _).values a (Fin.castSucc (Fin.last 0)) = _
      exact Norm38MacroCuts.snoc_previous a d1 _ (Fin.last 0)
    _ = base a := Norm38MacroPrefixFirst.first_prefix_value a

#print axioms d8_B
#print axioms d9_B
#print axioms d9_b
end DiophantineConsistency.Norm38MacroPrefixGroup03
