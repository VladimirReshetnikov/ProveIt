import PA194TransportSentence
import PA194FiniteAxioms
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqPASupplier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory PA194PAeq.language) [U.Δ₁]

theorem pa_axiom_cases (p : V) : p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class ↔
    (∃ σ ∈ PeanoMinus, p = (Encodable.encode σ : V)) ∨ InductionUnivR p := by
  change p ∈ (PeanoMinus ∪ InductionScheme ℒₒᵣ Set.univ).Δ₁Class ↔ _
  have hcases : p ∈ (PeanoMinus ∪ InductionScheme ℒₒᵣ Set.univ).Δ₁Class ↔
      p ∈ PeanoMinus.Δ₁Class ∨ p ∈ (InductionScheme ℒₒᵣ Set.univ).Δ₁Class := by
    change (V ⊧/![p] ((PeanoMinus.Δ₁ch ⋎ (InductionScheme ℒₒᵣ Set.univ).Δ₁ch).val)) ↔ _
    change (V ⊧/![p] ((PeanoMinus.Δ₁ch ⋎ (InductionScheme ℒₒᵣ Set.univ).Δ₁ch).val)) ↔ ((V ⊧/![p] PeanoMinus.Δ₁ch.val) ∨ (V ⊧/![p] (InductionScheme ℒₒᵣ Set.univ).Δ₁ch.val))
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  rw [hcases, PA194FiniteAxioms.peanoMinus_iff_sentence]
  have h : p ∈ (InductionScheme ℒₒᵣ Set.univ).Δ₁Class ↔ InductionUnivR p := by
    exact InductionUnivR.defined.df ![p]
  rw [h]

theorem supplier
    (hfinite : ∀ σ ∈ PeanoMinus, Provable U (formulaCode 0 (Encodable.encode σ : V)))
    (hind : ∀ p : V, InductionUnivR p → Provable U (formulaCode 0 p)) :
    ∀ p : V, p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class → Provable U (formulaCode 0 p) := by
  intro p hp
  rcases (pa_axiom_cases p).mp hp with ⟨σ,hσ,rfl⟩ | hi
  · exact hfinite σ hσ
  · exact hind p hi

theorem refutation_transport
    (hfinite : ∀ σ ∈ PeanoMinus, Provable U (formulaCode 0 (Encodable.encode σ : V)))
    (hind : ∀ p : V, InductionUnivR p → Provable U (formulaCode 0 p))
    (hp : Provable 𝗣𝗔 (qqFalsum : V)) : Provable U (qqFalsum : V) :=
  PA194PAeqTermBlueprint.refutation_transport 𝗣𝗔 U (supplier U hfinite hind) hp

#print axioms pa_axiom_cases
#print axioms supplier
#print axioms refutation_transport
end PA194PAeqPASupplier
