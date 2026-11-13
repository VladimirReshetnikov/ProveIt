import RingComparison88To87
import DiophantineConsistency.Compact44.P72Root

/-! Source-only forward positive witness map for omega=t+F. The graph
imports and ring comparison are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PositiveMap88To87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def forward (v : Fin 14 → V) : Fin 14 → V := Function.update v 13 (v 13+v 1)

theorem forward_positive (v : Fin 14 → V) (hv : ∀ j, 0<v j) :
    ∀ j, 0<forward v j := by
  intro j
  by_cases hj : j=13
  · subst j
    simpa [forward] using add_pos (hv 13) (hv 1)
  · simpa [forward,hj] using hv j

theorem cast_forward (v : Fin 14 → V) :
    (fun j => ι (forward v j)) = Ring88To87Draft.transform (fun j => ι (v j)) := by
  funext j
  by_cases hj : j=13
  · subst j
    simp [forward,Ring88To87Draft.transform,map_add]
  · simp [forward,Ring88To87Draft.transform,hj]

/-- Every positive 88 zero maps to a positive 87 zero. Integer ports are
arbitrary: no beta bound, calibration or port cast is needed. -/
theorem positive_map (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P87ShiftedGuard.graph p).output v' := by
  refine ⟨forward v,forward_positive v hv,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring88To87Draft.output_eval p (fun j => ι (v j))
  rw [←cast_forward v] at h
  rw [h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.PositiveMap88To87Draft

#print axioms DiophantineConsistency.PositiveMap88To87Draft.positive_map
