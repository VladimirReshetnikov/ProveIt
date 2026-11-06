import DiophantineConsistency.Norm38MacroDependentI

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent07
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d28_P_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d28.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d22.values a ((Fin.last 21)) := by
  calc
    d28.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d27.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d26.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d26 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc)
    _ = d25.values a ((Fin.last 21).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d25 _ ((Fin.last 21).castSucc.castSucc.castSucc)
    _ = d24.values a ((Fin.last 21).castSucc.castSucc) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 21).castSucc.castSucc)
    _ = d23.values a ((Fin.last 21).castSucc) := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ((Fin.last 21).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d23 _ ((Fin.last 21).castSucc)
    _ = d22.values a ((Fin.last 21)) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 21))) = _
      exact Norm38MacroCuts.snoc_previous a d22 _ ((Fin.last 21))

theorem d29_K_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d29.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d23.values a ((Fin.last 22)) := by
  calc
    d29.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d28.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d28 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc)
    _ = d26.values a ((Fin.last 22).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d26 _ ((Fin.last 22).castSucc.castSucc.castSucc)
    _ = d25.values a ((Fin.last 22).castSucc.castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d25 _ ((Fin.last 22).castSucc.castSucc)
    _ = d24.values a ((Fin.last 22).castSucc) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 22).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 22).castSucc)
    _ = d23.values a ((Fin.last 22)) := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ((Fin.last 22))) = _
      exact Norm38MacroCuts.snoc_previous a d23 _ ((Fin.last 22))


#print axioms d28_P_carry
#print axioms d29_K_carry
end DiophantineConsistency.Norm38MacroDependent07
