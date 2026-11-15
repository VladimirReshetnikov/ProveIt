import PA194PAeqOrdinaryTheoryDelta
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem inductionTheory_class (q : V) :
    letI := inductionTheoryDelta
    q ∈ inductionTheory.Δ₁Class ↔ ∃ p : V, IsSemiformula PA194PAeq.language 1 p ∧ closedInduction p = q := by
  letI := inductionTheoryDelta
  change V ⊧/![q] inductionUniform.val ↔ _
  letI : 𝚫₁-Predicate (inductionPure : V → Prop) via inductionUniform := inductionUniform_defined
  rw [HierarchySymbol.Defined.iff (φ := inductionUniform) (v := ![q])]
  exact inductionPure_iff q

theorem ordinaryPAeq_class (q : V) :
    letI := ordinaryPAeq_delta
    q ∈ ordinaryPAeq.Δ₁Class ↔
      q ∈ targetFixedTheory.Δ₁Class ∨ ∃ p : V, IsSemiformula PA194PAeq.language 1 p ∧ closedInduction p = q := by
  letI := ordinaryPAeq_delta
  change (V ⊧/![q] ((targetFixedTheory.Δ₁ch ⋎ inductionUniform).val)) ↔ _
  simp only [HierarchySymbol.Semiformula.val_or,LogicalConnective.HomClass.map_or,LogicalConnective.Prop.or_eq]
  change q ∈ targetFixedTheory.Δ₁Class ∨ (V ⊧/![q] inductionUniform.val) ↔ _
  letI : 𝚫₁-Predicate (inductionPure : V → Prop) via inductionUniform := inductionUniform_defined
  rw [HierarchySymbol.Defined.iff (φ := inductionUniform) (v := ![q]),inductionPure_iff]
  simp
#print axioms inductionTheory_class
#print axioms ordinaryPAeq_class
end generic
end PA194PAeqBind
