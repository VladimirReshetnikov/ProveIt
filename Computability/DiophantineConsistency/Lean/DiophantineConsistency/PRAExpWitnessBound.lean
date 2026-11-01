import DiophantineConsistency.PRAExponentialWitnessBound
import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRARewritingWitnessBound
/-! Bound Foundation expDef by the explicit exponential polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAExpWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] exponentialDef

theorem exp_bound (e n : V) : expDef.val.Evalb ![e,n] →
    (bnd expDef.val).Evalb ![e,n,PRAExponentialWitnessBound.exponentialMajorant e] := by
  intro h
  simp [expDef] at h ⊢
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hb := PRARewritingWitnessBound.binary_rew_bound_with exponentialDef.val
    (fun _ e => PRAExponentialWitnessBound.exponentialMajorant e)
    PRAExponentialWitnessBound.exponential_bound ω ![e,n]
    (PRAExponentialWitnessBound.exponentialMajorant e) (by simp [ω])
    (by simpa [ω, Semiformula.eval_substs] using h)
  simpa [ω] using hb
def boundedExp : ArithmeticSemisentence 3 := bnd expDef.val

def expBoundBody : ArithmeticSemisentence 2 :=
  “e n. !expDef e n → !boundedExp e n ((e⁴+1)+(e²+1)+(2*e²+1)+(e⁴+e⁴+2*e+1))”

theorem expBoundBody_model (v : Fin 2 → V) : expBoundBody.Eval v Empty.elim := by
  simp [expBoundBody, boundedExp, Semiformula.eval_substs]
  exact exp_bound (v 0) (v 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def expBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding expBoundBody

theorem candidate_proves_exp_bound : PRA ⊢ expBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact expBoundBody_model e
end DiophantineConsistency.PRAExpWitnessBound
