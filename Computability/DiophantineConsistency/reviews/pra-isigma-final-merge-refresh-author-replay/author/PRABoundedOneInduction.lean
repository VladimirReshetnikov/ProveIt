import DiophantineConsistency.PRAOpenOneInduction
import DiophantineConsistency.PRABoundedFormula
/-! One induction instance with a bounded matrix on x,y,c. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRABoundedOneInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAEqualityCode PRAOpenFormulaCoverage
  PRABoundedCharacteristic PRABoundedFormula PRAStageInductionSchema PRAFoundationOneInduction PRAOpenOneInduction

/-- A single induction instance can be eliminated whenever its matrix has an
actual candidate-PRA characteristic-code correctness proof. -/
theorem PRA_proves_goal_of_characteristicSuccInd (ψ : Semisentence language 3) (c : Code 3)
    (hc : PRA ⊢ characteristicSentence c ψ) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (openSigma ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ {(succInd (codedSigma c)).univCl}) ⊢ (∃⁰ θ).univCl := by
    letI : 𝗘𝗤 language ⪯ (PRA ∪ {(succInd (codedSigma c)).univCl}) :=
      Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro σ hσ
      exact hBoth.models _ (Or.inl hσ)
    have hchar := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
    have hcode : M↓[language] ⊧ (succInd (codedSigma c)).univCl := hBoth.models _ (Or.inr rfl)
    have hψ : M↓[language] ⊧ (succInd (openSigma ψ)).univCl := by
      apply (modelSuccInd_congr (openSigma ψ) (codedSigma c)
        (fun e x => modelSigmaCharacteristic ψ c hchar e x)).mpr
      exact hcode
    have hPlus : M↓[language] ⊧* (PRA ∪ {(succInd (openSigma ψ)).univCl}) := by
      constructor
      intro σ hσ
      rcases hσ with hσ | hσ
      · exact (inferInstance : M↓[language] ⊧* PRA).models _ hσ
      · simp only [Set.mem_singleton_iff] at hσ
        subst σ
        exact hψ
    exact models_of_provable hPlus p
  exact PRA_proves_goal_of_succInd c θ hθ hp

/-- Eliminate one actual Foundation successor-induction instance for the
Σ₁ predicate ∃y ψ(x,y,c), for any bounded ψ on precisely those inputs. -/
theorem PRA_proves_goal_of_boundedSuccInd (ψ : Semisentence language 3)
    (hψ : Hierarchy 𝚺 0 ψ) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ {(succInd (openSigma ψ)).univCl}) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨c,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic ψ hψ
  have hc' : PRA ⊢ characteristicSentence c ψ := hc
  exact PRA_proves_goal_of_characteristicSuccInd ψ c hc' θ hθ p
end DiophantineConsistency.PRABoundedOneInduction
