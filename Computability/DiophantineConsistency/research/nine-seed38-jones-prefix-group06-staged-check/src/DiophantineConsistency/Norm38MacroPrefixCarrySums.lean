import DiophantineConsistency.Norm38MacroPrefixQNCarry

/-! Candidate preservation of d10 entries; sums remain named prefix values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup06
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d10_e_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc.castSucc) = d5.values a ((Fin.last 4)) := by
  calc
    d10.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 4).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d9 _ ((Fin.last 4).castSucc.castSucc.castSucc.castSucc)
    _ = d8.values a ((Fin.last 4).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 4).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d8 _ ((Fin.last 4).castSucc.castSucc.castSucc)
    _ = d7.values a ((Fin.last 4).castSucc.castSucc) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 4).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d7 _ ((Fin.last 4).castSucc.castSucc)
    _ = d6.values a ((Fin.last 4).castSucc) := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ((Fin.last 4).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d6 _ ((Fin.last 4).castSucc)
    _ = d5.values a ((Fin.last 4)) := by
      change (Dag.snoc d5 _).values a (Fin.castSucc ((Fin.last 4))) = _
      exact Norm38MacroCuts.snoc_previous a d5 _ ((Fin.last 4))

theorem d10_ell_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 5).castSucc.castSucc.castSucc.castSucc) = d6.values a ((Fin.last 5)) := by
  calc
    d10.values a ((Fin.last 5).castSucc.castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 5).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 5).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d9 _ ((Fin.last 5).castSucc.castSucc.castSucc)
    _ = d8.values a ((Fin.last 5).castSucc.castSucc) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 5).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d8 _ ((Fin.last 5).castSucc.castSucc)
    _ = d7.values a ((Fin.last 5).castSucc) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 5).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d7 _ ((Fin.last 5).castSucc)
    _ = d6.values a ((Fin.last 5)) := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ((Fin.last 5))) = _
      exact Norm38MacroCuts.snoc_previous a d6 _ ((Fin.last 5))

theorem d10_lambda_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d10.values a ((Fin.last 6).castSucc.castSucc.castSucc) = d7.values a ((Fin.last 6)) := by
  calc
    d10.values a ((Fin.last 6).castSucc.castSucc.castSucc) =
        d9.values a ((Fin.last 6).castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 6).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d9 _ ((Fin.last 6).castSucc.castSucc)
    _ = d8.values a ((Fin.last 6).castSucc) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 6).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d8 _ ((Fin.last 6).castSucc)
    _ = d7.values a ((Fin.last 6)) := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ((Fin.last 6))) = _
      exact Norm38MacroCuts.snoc_previous a d7 _ ((Fin.last 6))

#print axioms d10_e_carry
#print axioms d10_ell_carry
#print axioms d10_lambda_carry
end DiophantineConsistency.Norm38MacroPrefixGroup06
