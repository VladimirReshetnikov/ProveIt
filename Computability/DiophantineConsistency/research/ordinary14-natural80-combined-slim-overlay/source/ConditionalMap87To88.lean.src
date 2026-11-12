import PositiveMap88To87

/-! Source-only conditional reverse guard shift. The strict omega>F
hypothesis is not derived here; no Lean or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ConditionalMap87To88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def reverse (v : Fin 14 → V) : Fin 14 → V := Function.update v 13 (v 13-v 1)

theorem reverse_positive (v : Fin 14 → V) (hv : ∀ j, 0<v j)
    (hstrict : v 1<v 13) : ∀ j, 0<reverse v j := by
  intro j
  by_cases hj : j=13
  · subst j
    simpa [reverse] using tsub_pos_of_lt hstrict
  · simpa [reverse,hj] using hv j

theorem cast_reverse (v : Fin 14 → V) (hstrict : v 1<v 13) :
    (fun j => ι (v j)) = Ring88To87Draft.transform (fun j => ι (reverse v j)) := by
  have hd : ι (v 13-v 1)=ι (v 13)-ι (v 1) := P72Root.ι_tsub (le_of_lt hstrict)
  funext j
  by_cases hj : j=13
  · subst j
    simp [reverse,Ring88To87Draft.transform,map_add,hd] <;> ring
  · simp [reverse,Ring88To87Draft.transform,hj]

/-- A positive 87 zero with omega>F yields a positive 88 zero. -/
theorem positive_map (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hv : ∀ j, 0<v j) (hstrict : v 1<v 13)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P88QuotientGuarded.graph p).output v' := by
  refine ⟨reverse v,reverse_positive v hv hstrict,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring88To87Draft.output_eval p (fun j => ι (reverse v j))
  rw [←cast_reverse v hstrict] at h
  rw [←h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.ConditionalMap87To88Draft

#print axioms DiophantineConsistency.ConditionalMap87To88Draft.positive_map
