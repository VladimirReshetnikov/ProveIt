import Ring75To74
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.Compact44.P72Root

/-! Source-only positive witness maps. Reverse transfer explicitly assumes
that the 74 guard coordinate exceeds one. Imported drafts are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Positive75To74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def forward (v : Fin 14 → V) : Fin 14 → V := Function.update v 13 (v 13+1)
def reverse (v : Fin 14 → V) : Fin 14 → V := Function.update v 13 (v 13-1)

theorem forward_positive (v : Fin 14 → V) (hv : ∀ j, 0<v j) :
    ∀ j, 0<forward v j := by
  intro j
  by_cases hj : j=13
  · subst j
    simpa [forward] using add_pos (hv 13) (show (0:V)<1 by simp)
  · simpa [forward,hj] using hv j

theorem cast_forward (v : Fin 14 → V) :
    (fun j => ι (forward v j))=Ring75To74Draft.transform (fun j => ι (v j)) := by
  funext j
  by_cases hj : j=13
  · subst j
    simp [forward,Ring75To74Draft.transform,map_add]
  · simp [forward,Ring75To74Draft.transform,hj]

theorem forward_map (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P75NegativePell.graph p).output v) :
    ∃ w : Fin 14 → V, (∀ j, 0<w j) ∧ InternalZero (P74PositiveGuard.graph p).output w := by
  refine ⟨forward v,forward_positive v hv,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring75To74Draft.output_eval p (fun j => ι (v j))
  rw [←cast_forward v] at h
  rw [h]
  exact (internalZero_iff _ _).mp hz

theorem reverse_positive (v : Fin 14 → V) (hv : ∀ j, 0<v j) (hstrict : 1<v 13) :
    ∀ j, 0<reverse v j := by
  intro j
  by_cases hj : j=13
  · subst j
    simpa [reverse] using tsub_pos_of_lt hstrict
  · simpa [reverse,hj] using hv j

/-- Strictness justifies the natural subtraction and the ring update. -/
theorem cast_reverse (v : Fin 14 → V) (hstrict : 1<v 13) :
    (fun j => ι (v j))=Ring75To74Draft.transform (fun j => ι (reverse v j)) := by
  have hd : ι (v 13-1)=ι (v 13)-1 := by
    simpa only [map_one] using (P72Root.ι_tsub (le_of_lt hstrict))
  funext j
  by_cases hj : j=13
  · subst j
    simp [reverse,Ring75To74Draft.transform,hd] <;> ring
  · simp [reverse,Ring75To74Draft.transform,hj]

/-- Reverse transfer remains conditional on the 74 own coordinate bound. -/
theorem reverse_map (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hv : ∀ j, 0<v j) (hstrict : 1<v 13)
    (hz : InternalZero (P74PositiveGuard.graph p).output v) :
    ∃ w : Fin 14 → V, (∀ j, 0<w j) ∧ InternalZero (P75NegativePell.graph p).output w := by
  refine ⟨reverse v,reverse_positive v hv hstrict,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring75To74Draft.output_eval p (fun j => ι (reverse v j))
  rw [←cast_reverse v hstrict] at h
  rw [←h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.Positive75To74Draft

#print axioms DiophantineConsistency.Positive75To74Draft.forward_map
#print axioms DiophantineConsistency.Positive75To74Draft.reverse_map
