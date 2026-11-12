import P79NaturalForcedW
import P80NaturalForcedGamma
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only 79-to-80 w-shift proposal. The model existence equivalence
explicitly assumes the missing positive-w theorem for every 79 zero. No
Lean elaboration, iPRA derivation, or external byte binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural79WShiftDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing

/-- The 80 input is the 79 input minus one at the w slot. -/
def down80 {R : Type*} [Sub R] [One R] (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 6 then v j - 1 else v j

/-- Exact ring comparison at related valuations, not at the same valuation. -/
theorem output_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P79NaturalForcedW.graph p).output.evalRing v =
      (P80NaturalForcedGamma.graph p).output.evalRing (down80 v) := by
  simp [P79NaturalForcedW.graph, P80NaturalForcedGamma.graph, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, down80]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 79 coordinate is the successor of the corresponding 80 coordinate. -/
def Related (v79 v80 : Fin 14 → V) : Prop :=
  v79 6 = v80 6 + 1 ∧ ∀ j, j ≠ 6 → v79 j = v80 j

def lift (v : Fin 14 → V) : Fin 14 → V :=
  fun j => if j = 6 then v j + 1 else v j

theorem related_lift (v : Fin 14 → V) : Related (lift v) v := by
  constructor
  · simp [lift]
  · intro j hj; simp [lift, hj]

theorem related_embedding {v79 v80 : Fin 14 → V} (h : Related v79 v80) :
    down80 (fun j => ι (v79 j)) = (fun j => ι (v80 j)) := by
  funext j
  fin_cases j <;> simp_all [Related, down80, map_add, map_one]

/-- Proposed model comparison only for related valuations. -/
theorem internalZero_iff_related (p : Fin 4 → ℤ) {v79 v80 : Fin 14 → V}
    (h : Related v79 v80) :
    InternalZero (P79NaturalForcedW.graph p).output v79 ↔
      InternalZero (P80NaturalForcedGamma.graph p).output v80 := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    output_eval, related_embedding h]

/-- Conditional transfer. No source theorem in this packet proves the
positive-w hypothesis or its necessary represented-port assumptions. -/
theorem exists_zero_iff_of_positive (p : Fin 4 → ℤ)
    (positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6) :
    (∃ v, InternalZero (P79NaturalForcedW.graph p).output v) ↔
      ∃ w, InternalZero (P80NaturalForcedGamma.graph p).output w := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨z, hz⟩ := exists_add_of_le (pos_iff_one_le.mp (positive_w v hv))
    let w : Fin 14 → V := fun j => if j = 6 then z else v j
    have hw : Related v w := by
      constructor
      · simpa [w, add_comm] using hz
      · intro j hj; simp [w, hj]
    exact ⟨w, (internalZero_iff_related p hw).mp hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨lift w, (internalZero_iff_related p (related_lift w)).mpr hw⟩

end DiophantineConsistency.Natural79WShiftDraft

#print axioms DiophantineConsistency.Natural79WShiftDraft.output_eval
#print axioms DiophantineConsistency.Natural79WShiftDraft.internalZero_iff_related
#print axioms DiophantineConsistency.Natural79WShiftDraft.exists_zero_iff_of_positive
