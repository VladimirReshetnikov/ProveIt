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
  exact PRAOpenOneInduction.PRA_proves_goal_of_characteristicSuccInd ψ c hc θ hθ p

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
