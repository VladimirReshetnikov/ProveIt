import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRANegExponentialWitnessBound
/-! Bound the negative Foundation expDef graph by an explicit polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegExpWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] exponentialDef

theorem neg_exp_bound (e n : V) : (∼expDef.val).Evalb ![e,n] →
    (bnd (∼expDef.val)).Evalb ![e,n,PRANegExponentialWitnessBound.negExponentialMajorant e] := by
  intro h
  simp [expDef] at h ⊢
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
  have h' : (∼exponentialDef.val).Evalb ![n,e] := by simpa using h
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hf : (ω ▹ (∼exponentialDef.val)).Evalb ![e,n] := by
    simpa [ω, Semiformula.eval_substs] using h'
  have hw : PRANegExponentialWitnessBound.negExponentialMajorant
      ((ω #1).val ![e,n] Empty.elim) ≤ PRANegExponentialWitnessBound.negExponentialMajorant e := by
    simp [ω]
  have hrew := PRARewritingWitnessBound.binary_rew_bound_with (∼exponentialDef.val)
    (fun _ e => PRANegExponentialWitnessBound.negExponentialMajorant e)
    PRANegExponentialWitnessBound.negExponential_bound ω ![e,n]
    (PRANegExponentialWitnessBound.negExponentialMajorant e) hw hf
  rw [show (ω ▹ (∼exponentialDef.val)) = ∼(ω ▹ exponentialDef.val) from
    LogicalConnective.HomClass.map_neg (Semiformula.rew ω) exponentialDef.val] at hrew
  simpa using hrew
def negExp : ArithmeticSemisentence 2 := ∼expDef.val

def boundedNegExp : ArithmeticSemisentence 3 := bnd negExp

def negExpBoundBody : ArithmeticSemisentence 2 :=
  “e n. !negExp e n → !boundedNegExp e n ((2*e+1)+(2*e²+1))”

theorem negExpBoundBody_model (v : Fin 2 → V) : negExpBoundBody.Eval v Empty.elim := by
  simp [negExpBoundBody, boundedNegExp, Semiformula.eval_substs]
  exact neg_exp_bound (v 0) (v 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negExpBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negExpBoundBody

theorem candidate_proves_negExp_bound : PRA ⊢ negExpBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negExpBoundBody_model e
end DiophantineConsistency.PRANegExpWitnessBound
