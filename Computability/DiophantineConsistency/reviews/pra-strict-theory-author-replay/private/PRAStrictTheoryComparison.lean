import DiophantineConsistency.PRAStrictSigmaFiniteClient
import DiophantineConsistency.PRAISigmaOneFiniteTranslation
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAStrictTheoryComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPeanoMinusTranslation ParsonsTheoryNormalize
  PRAISigmaOneFiniteTranslation PRAStrictSigmaFiniteClient

def strictTheory : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictCase

theorem strictCase_sigma (φ : ArithmeticSemiformula ℕ 1) (hφ : StrictCase φ) :
    Hierarchy 𝚺 1 φ := by
  rcases hφ with hφ | ⟨D,hD,rfl⟩
  · exact hφ.mono (by decide)
  · exact Hierarchy.exs (hD.mono (by decide))

theorem strictTheory_subset_isigmaOne : strictTheory ⊆ 𝗜𝚺₁ := by
  intro σ hσ
  rcases hσ with hσ | ⟨φ,hφ,rfl⟩
  · exact Or.inl hσ
  · exact Or.inr ⟨φ,strictCase_sigma φ hφ,rfl⟩

theorem finite_translation {σ : ArithmeticSentence} (p : Theory.Proof strictTheory σ) :
    ∃ Φ : List (ArithmeticSemiformula ℕ 1),
      (∀ φ ∈ Φ, StrictCase φ) ∧
      (PRA ∪ mappedInductions Φ) ⊢ Semiformula.lMap embedding σ := by
  obtain ⟨B,Φ,hB,hΦ,hcover⟩ := partition 𝗣𝗔⁻ StrictCase p.axioms p.axioms_mem
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
/-- A proof over PA-minus plus the strict syntactic induction scheme translates
into candidate PRA for any exactly mapped universally closed open-existential goal. -/
theorem comparison (σ : ArithmeticSentence) (p : Theory.Proof strictTheory σ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (hgoal : Semiformula.lMap embedding σ = (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨Φ,hΦ,hproof⟩ := finite_translation p
  rw [hgoal] at hproof
  exact PRA_proves_goal_of_finite_strict Φ hΦ θ hθ hproof
end DiophantineConsistency.PRAStrictTheoryComparison
