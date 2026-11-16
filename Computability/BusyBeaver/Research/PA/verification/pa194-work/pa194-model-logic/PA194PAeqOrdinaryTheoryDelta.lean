import PA194PAeqInductionTheoryTyped
import PA194PAeqTargetAxiom
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq

theorem ordinaryPAeq_eq_union : ordinaryPAeq = targetFixedTheory ∪ inductionTheory := by
  ext σ
  constructor
  · rintro ⟨p,hp,rfl⟩
    cases hp with
    | fixed p hp =>
      left
      change p.univCl ∈ targetFixedSentences
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    | induction p =>
      right
      exact inductionTheory_mem_iff_typed _ |>.mpr ⟨p,rfl⟩
  · rintro (hf | hi)
    · exact targetFixed_subset_ordinary hf
    · obtain ⟨p,rfl⟩ := (inductionTheory_mem_iff_typed σ).mp hi
      exact ⟨inductionFormula p,PAeqAxiom.induction p,rfl⟩
noncomputable instance ordinaryPAeq_delta : ordinaryPAeq.Δ₁ :=
  Theory.Δ₁.ofEq (Theory.Δ₁.add targetFixedTheory_delta1 inductionTheoryDelta) ordinaryPAeq_eq_union.symm
#print axioms ordinaryPAeq_eq_union
#print axioms ordinaryPAeq_delta
end PA194PAeqBind
