import RingNatural82To86
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only model proposal. The positivity/predecessor premise in the
existence theorem is explicitly assumed, not proved in this file. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural82ModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing RingNatural82To86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 82 valuation is one greater exactly in slots f, r and y. -/
def Related (v82 v86 : Fin 14 → V) : Prop :=
  v82 3 = v86 3 + 1 ∧ v82 8 = v86 8 + 1 ∧ v82 11 = v86 11 + 1 ∧
    ∀ j, j ≠ 3 → j ≠ 8 → j ≠ 11 → v82 j = v86 j

def lift (v : Fin 14 → V) : Fin 14 → V :=
  fun j => if j = 3 ∨ j = 8 ∨ j = 11 then v j + 1 else v j

theorem related_lift (v : Fin 14 → V) : Related (lift v) v := by
  simp only [Related, lift]
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  · intro j h3 h8 h11
    simp [h3, h8, h11]

/-- A related natural valuation supplies the ring subtraction. -/
theorem related_embedding {v82 v86 : Fin 14 → V} (h : Related v82 v86) :
    down (fun j => ι (v82 j)) = (fun j => ι (v86 j)) := by
  funext j
  fin_cases j <;> simp_all [Related, down, map_add, map_one]

theorem internalZero_iff_of_related (p : Fin 4 → ℤ) {v82 v86 : Fin 14 → V}
    (h : Related v82 v86) :
    InternalZero (P82NaturalForced.graph p).output v82 ↔
      InternalZero (P86NaturalCancel.graph p).output v86 := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    RingNatural82To86Draft.output_eval, related_embedding h]

/-- Successors are the precise model-side obligation for an 82 zero. -/
def HasThreePredecessors (v : Fin 14 → V) : Prop :=
  ∃ f r y : V, v 3 = f + 1 ∧ v 8 = r + 1 ∧ v 11 = y + 1

theorem related_of_predecessors (v : Fin 14 → V) (h : HasThreePredecessors v) :
    ∃ w, Related v w := by
  obtain ⟨f, r, y, hf, hr, hy⟩ := h
  let w : Fin 14 → V := fun j => if j = 3 then f else if j = 8 then r else if j = 11 then y else v j
  refine ⟨w, ?_⟩
  simp only [Related]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [w] using hf
  · simpa [w] using hr
  · simpa [w] using hy
  · intro j h3 h8 h11
    simp [w, h3, h8, h11]

/-- Conditional only: no proof of the predecessor premise is claimed. -/
theorem exists_zero_iff_of_predecessors (p : Fin 4 → ℤ)
    (predecessors : ∀ v, InternalZero (P82NaturalForced.graph p).output v →
      HasThreePredecessors v) :
    (∃ v, InternalZero (P82NaturalForced.graph p).output v) ↔
      ∃ w, InternalZero (P86NaturalCancel.graph p).output w := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := related_of_predecessors v (predecessors v hv)
    exact ⟨w, (internalZero_iff_of_related p hw).mp hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨lift w, (internalZero_iff_of_related p (related_lift w)).mpr hw⟩

end DiophantineConsistency.Natural82ModelDraft
