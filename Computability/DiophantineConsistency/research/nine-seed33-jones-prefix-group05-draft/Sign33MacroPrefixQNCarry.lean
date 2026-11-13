import DiophantineConsistency.Sign33MacroPrefixGlarge

/-! Candidate preservation of q and N at d10; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup05
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 ExecutableJones

theorem d10_q {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat) := by
  calc
    d10.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d8.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d8 _ ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d7.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 2).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d7 _ ((Fin.last 2).castSucc.castSucc.castSucc.castSucc)
    _ = d6.values a ((Fin.last 2).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ((Fin.last 2).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d6 _ ((Fin.last 2).castSucc.castSucc.castSucc)
    _ = d5.values a ((Fin.last 2).castSucc.castSucc) := by
      change (Dag.snoc d5 _).values a (Fin.castSucc ((Fin.last 2).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d5 _ ((Fin.last 2).castSucc.castSucc)
    _ = d4.values a ((Fin.last 2).castSucc) := by
      change (Dag.snoc d4 _).values a (Fin.castSucc ((Fin.last 2).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d4 _ ((Fin.last 2).castSucc)
    _ = d3.values a ((Fin.last 2)) := by
      change (Dag.snoc d3 _).values a (Fin.castSucc ((Fin.last 2))) = _
      exact Sign33MacroCuts.snoc_previous a d3 _ ((Fin.last 2))
    _ = (base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat) := prefix_q a

theorem d10_N {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := by
  calc
    d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d8.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d8 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc)
    _ = d7.values a ((Fin.last 3).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d7 _ ((Fin.last 3).castSucc.castSucc.castSucc)
    _ = d6.values a ((Fin.last 3).castSucc.castSucc) := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d6 _ ((Fin.last 3).castSucc.castSucc)
    _ = d5.values a ((Fin.last 3).castSucc) := by
      change (Dag.snoc d5 _).values a (Fin.castSucc ((Fin.last 3).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d5 _ ((Fin.last 3).castSucc)
    _ = d4.values a ((Fin.last 3)) := by
      change (Dag.snoc d4 _).values a (Fin.castSucc ((Fin.last 3))) = _
      exact Sign33MacroCuts.snoc_previous a d4 _ ((Fin.last 3))
    _ = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := prefix_N a

#print axioms d10_q
#print axioms d10_N
end DiophantineConsistency.Sign33MacroPrefixGroup05
