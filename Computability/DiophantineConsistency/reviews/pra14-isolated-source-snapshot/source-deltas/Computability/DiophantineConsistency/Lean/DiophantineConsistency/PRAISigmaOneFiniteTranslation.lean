import DiophantineConsistency.ParsonsTheoryNormalize
import DiophantineConsistency.ParsonsMapInduction
import DiophantineConsistency.PRAPeanoMinusTranslation
/-! Extract the finite induction instances actually used by an IΣ₁ proof and
translate its conclusion to candidate PRA plus their mapped instances. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAISigmaOneFiniteTranslation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPeanoMinusTranslation ParsonsTheoryNormalize

def mappedInduction (φ : ArithmeticSemiformula ℕ 1) : Sentence language :=
  (Semiformula.lMap embedding (succInd φ)).univCl

def mappedInductions (Φ : List (ArithmeticSemiformula ℕ 1)) : Theory language :=
  {σ | ∃ φ ∈ Φ, σ = mappedInduction φ}

theorem finite_translation {σ : ArithmeticSentence} (p : Theory.Proof 𝗜𝚺₁ σ) :
    ∃ Φ : List (ArithmeticSemiformula ℕ 1),
      (∀ φ ∈ Φ, Hierarchy 𝚺 1 φ) ∧
      (PRA ∪ mappedInductions Φ) ⊢ Semiformula.lMap embedding σ := by
  obtain ⟨B,Φ,hB,hΦ,hcover⟩ := partition 𝗣𝗔⁻ (Hierarchy 𝚺 1) p.axioms p.axioms_mem
  refine ⟨Φ,hΦ,?_⟩
  letI : 𝗘𝗤 language ⪯ (PRA ∪ mappedInductions Φ) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hBoth
  letI : M↓[language] ⊧* PRA := by
    constructor
    intro τ hτ
    exact hBoth.models _ (Or.inl hτ)
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
    constructor
    intro τ hτ
    have hp := PRA_proves_peanoMinusAxiom hτ
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
    exact Semiformula.models_lMap.mp hm
  have haxioms : ∀ τ ∈ p.axioms, M↓[ℒₒᵣ] ⊧ τ := by
    intro τ hτ
    have hh := hcover hτ
    simp only [List.mem_append, List.mem_map] at hh
    rcases hh with hh | ⟨φ,hφ,rfl⟩
    · exact hPA.models _ (hB τ hh)
    · have hm : M↓[language] ⊧ mappedInduction φ :=
        hBoth.models _ (Or.inr ⟨φ,hφ,rfl⟩)
      simp only [mappedInduction, models_iff, Semiformula.eval_univCl] at hm
      simp only [models_iff, Semiformula.eval_univCl]
      intro e
      exact Semiformula.eval_lMap.mp (hm e)
  have hp : Theory.Proof {τ | M↓[ℒₒᵣ] ⊧ τ} σ := ⟨p.axioms,haxioms,p.derivation⟩
  have hmodel : M↓[ℒₒᵣ] ⊧* {τ | M↓[ℒₒᵣ] ⊧ τ} := ⟨fun _ h => h⟩
  exact Semiformula.models_lMap.mpr (models_of_provable hmodel ⟨hp⟩)
end DiophantineConsistency.PRAISigmaOneFiniteTranslation
