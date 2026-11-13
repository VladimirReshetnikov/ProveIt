import DiophantineConsistency.Norm38MacroVarsDm

/-! Candidate Kc cut from the divisor and margin bindings. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroVarsKc
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroDependent08 Norm38MacroVarsBd

theorem d43_Kc_eq {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d43.values a (Fin.last 42) = (vars a).dvsr * (((2 : Int) : R) * (vars a).marg - ((1 : Int) : R)) := by
  have hB : d42.values a ⟨39, by decide⟩ = (vars a).dvsr := by
    have hi : (⟨39, by decide⟩ : Fin 42) = ((⟨39, by decide⟩ : Fin 41).castSucc) := by decide
    rw [hi]
    change (Dag.snoc d41 _).values a (Fin.castSucc (⟨39, by decide⟩ : Fin 41)) = _
    rw [Norm38MacroCuts.snoc_previous, d41_Bd_eq_dvsr]
  have hiD : (⟨41, by decide⟩ : Fin 42) = Fin.last 41 := by decide
  rw [prefix_Kc, hB, hiD, d42_Dm_eq_marg]

#print axioms d43_Kc_eq
end DiophantineConsistency.Norm38MacroVarsKc
