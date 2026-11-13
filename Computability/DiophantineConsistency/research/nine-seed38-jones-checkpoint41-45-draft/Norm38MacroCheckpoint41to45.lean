import DiophantineConsistency.Norm38MacroCheckpoint34to41
import DiophantineConsistency.Norm38MacroLive18Group01
import DiophantineConsistency.Norm38MacroLive18Group02
import DiophantineConsistency.Norm38MacroPrefixGsmall
import DiophantineConsistency.Norm38MacroPrefixGlarge

/-! Candidate final checkpoint and symbolic g/G values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpoint41to45
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding
  Norm38MacroPath18to41 Norm38MacroLive18 Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup03

theorem path41_45 : PrefixPath d41 d45 (fun i => i.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d41 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d41 _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d41) _) _) _) _)

theorem lookup41_45 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 41) :
    d45.values a i.castSucc.castSucc.castSucc.castSucc = d41.values a i := by
  exact lookup path41_45 a i

theorem lookup_recipe41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 41) :
    Norm38MacroRecipe.recipe.values a i.castSucc.castSucc.castSucc.castSucc = d41.values a i := by
  rw [recipe_eq_named]
  exact lookup41_45 a i

theorem d41_g_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨1, by decide⟩ + ((1 : Int) : R) := by
  calc
    d41.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup18_41 a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 7).castSucc.castSucc.castSucc) := d18_g_carry a
    _ = d10.values a ((Fin.last 7).castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d10 _ ((Fin.last 7).castSucc.castSucc)
    _ = d9.values a ((Fin.last 7).castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 7).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d9 _ ((Fin.last 7).castSucc)
    _ = d8.values a ((Fin.last 7)) := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ((Fin.last 7))) = _
      exact Norm38MacroCuts.snoc_previous a d8 _ ((Fin.last 7))
    _ = a ⟨1, by decide⟩ + ((1 : Int) : R) := prefix_g a

theorem d41_G_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((32 : Int) : R) * base a * (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat) := by
  calc
    d41.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup18_41 a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 9).castSucc) := d18_G_carry a
    _ = d10.values a ((Fin.last 9)) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 9))) = _
      exact Norm38MacroCuts.snoc_previous a d10 _ ((Fin.last 9))
    _ = ((32 : Int) : R) * base a * (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat) := prefix_G a

#print axioms path41_45
#print axioms lookup41_45
#print axioms lookup_recipe41
#print axioms d41_g_value
#print axioms d41_G_value
end DiophantineConsistency.Norm38MacroCheckpoint41to45
