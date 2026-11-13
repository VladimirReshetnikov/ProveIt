import DiophantineConsistency.Sign33MacroPrefixQNCarry

/-! Candidate preservation of d10 entries; sums remain named prefix values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup06
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d10_g_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 7).castSucc.castSucc) = d8.values a ((Fin.last 7)) := by
  calc
    d10.values a ((Fin.last 7).castSucc.castSucc) =
        d9.values a ((Fin.last 7).castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 7).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 7).castSucc)
    _ = d8.values a ((Fin.last 7)) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 7))) = _
      exact Sign33MacroCuts.snoc_previous a d8 _ ((Fin.last 7))

theorem d10_theta_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 8).castSucc) = d9.values a ((Fin.last 8)) := by
  calc
    d10.values a ((Fin.last 8).castSucc) =
        d9.values a ((Fin.last 8)) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 8))) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 8))

theorem d10_B_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d9.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d10.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d10_b_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

#print axioms d10_g_carry
#print axioms d10_theta_carry
#print axioms d10_B_carry
#print axioms d10_b_carry
end DiophantineConsistency.Sign33MacroPrefixGroup06
