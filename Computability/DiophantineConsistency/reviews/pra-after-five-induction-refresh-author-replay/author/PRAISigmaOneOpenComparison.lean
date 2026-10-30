import DiophantineConsistency.StrictSigmaOneInduction
import DiophantineConsistency.PRAPositiveStrictCertificate
import DiophantineConsistency.ParsonsPositiveRule
import DiophantineConsistency.PRAISigmaOneFiniteTranslation
/-! Combine strict-prefix normalization and finite positive-axiom elimination. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAISigmaOneOpenComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPeanoMinusTranslation ParsonsTheoryNormalize
  PRAISigmaOneFiniteTranslation PRAConditionalSigmaNormalization
  StrictSigmaOneInduction PRAPositiveStrictCertificate

def prefixTheory : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma

theorem finite_strict_translation {σ : ArithmeticSentence} (p : Theory.Proof prefixTheory σ) :
    ∃ Φ : List (ArithmeticSemiformula ℕ 1),
      (∀ φ ∈ Φ, StrictSigma φ) ∧
      (PRA ∪ mappedInductions Φ) ⊢ Semiformula.lMap embedding σ := by
  obtain ⟨B,Φ,hB,hΦ,hcover⟩ := partition 𝗣𝗔⁻ StrictSigma p.axioms p.axioms_mem
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
/-- IΣ₁'s open-existential consequences transfer to candidate PRA when the
actual mapped conclusion implies the chosen candidate-language goal in PRA. -/
theorem comparison (σ : ArithmeticSentence) (p : 𝗜𝚺₁ ⊢ σ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (hgoal : PRA ⊢ (Semiformula.lMap embedding σ 🡒 (∃⁰ θ).univCl)) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨p'⟩ := isigma1_provable p
  obtain ⟨Φ,hΦ,hproof⟩ := finite_strict_translation p'
  have hnormalized : (PRA ∪ mappedInductions Φ) ⊢ (∃⁰ θ).univCl := by
    letI : 𝗘𝗤 language ⪯ (PRA ∪ mappedInductions Φ) :=
      Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro τ hτ
      exact hBoth.models _ (Or.inl hτ)
    have hg := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hgoal
    have hs := models_of_provable hBoth hproof
    simp only [Semantics.Imp.models_imply] at hg
    exact hg hs
  apply PRA_proves_goal_of_certificates Φ _ θ hθ hnormalized
  intro φ hφ
  apply positive_certificate φ
  apply ParsonsPositiveRule.strict_positive
  exact hΦ φ hφ
end DiophantineConsistency.PRAISigmaOneOpenComparison
