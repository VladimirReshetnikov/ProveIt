import DiophantineConsistency.PRAStrictSigmaCertificate
import DiophantineConsistency.ParsonsISigmaZeroComparison
/-! Eliminate a finite set of mapped induction axioms for bounded predicates
or predicates explicitly of the form ∃ over a bounded matrix. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStrictSigmaFiniteClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRABoundedInduction PRAConditionalSigmaNormalization
  PRAISigmaOneFiniteTranslation PRAFiniteMultiParameterInduction PRAStrictSigmaCertificate

def StrictCase (φ : ArithmeticSemiformula ℕ 1) : Prop :=
  Hierarchy 𝚺 0 φ ∨ ∃ D : ArithmeticSemiformula ℕ 2, Hierarchy 𝚺 0 D ∧ φ = ∃⁰ D

theorem bounded_certificate (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 0 φ) : Certificate φ := by
  let d : Descriptor := ⟨0, ⊤⟩
  have hp : PRA ⊢ mappedInduction φ := by
    unfold mappedInduction
    rw [ParsonsMapInduction.map_succInd]
    exact PRA_proves_boundedInduction (Semiformula.lMap embedding φ) (ParsonsHierarchyMap.hierarchy hφ)
  refine ⟨d, Hierarchy.verum _ _ _, ?_⟩
  exact Entailment.weakening (Entailment.WeakerThan.ofSubset (fun _ h => Or.inl h)) hp

theorem case_certificate (φ : ArithmeticSemiformula ℕ 1) (hφ : StrictCase φ) : Certificate φ := by
  rcases hφ with hφ | ⟨D,hD,rfl⟩
  · exact bounded_certificate φ hφ
  · exact strict_certificate D hD

theorem PRA_proves_goal_of_finite_strict
    (Φ : List (ArithmeticSemiformula ℕ 1)) (hΦ : ∀ φ ∈ Φ, StrictCase φ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ mappedInductions Φ) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl :=
  PRA_proves_goal_of_certificates Φ (fun φ hφ => case_certificate φ (hΦ φ hφ)) θ hθ p
end DiophantineConsistency.PRAStrictSigmaFiniteClient
