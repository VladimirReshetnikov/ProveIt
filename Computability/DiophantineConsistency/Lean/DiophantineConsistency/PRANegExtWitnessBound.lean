import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAExponentialWitnessBound
/-! Bound negative Foundation extDef at any witness limit; the negative
    exponential and bit bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegExtWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_ext_bound (a b c w : V) : (∼extDef.val).Evalb ![a,b,c] →
    (bnd (∼extDef.val)).Evalb ![a,b,c,w] := by
  intro h
  simp [extDef, divDef, remDef, subDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, DeMorgan.imply, bnd, bnd_open, Rew.subst, Rew.q] at h ⊢
  exact h
def negExt : ArithmeticSemisentence 3 := ∼extDef.val

def boundedNegExt : ArithmeticSemisentence 4 := bnd negExt

def negExtBoundBody : ArithmeticSemisentence 4 :=
  “a b c w. !negExt a b c → !boundedNegExt a b c w”

theorem negExtBoundBody_model (e : Fin 4 → V) : negExtBoundBody.Eval e Empty.elim := by
  simp [negExtBoundBody, boundedNegExt, Semiformula.eval_substs]
  exact neg_ext_bound (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negExtBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negExtBoundBody

theorem candidate_proves_negExt_bound : PRA ⊢ negExtBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negExtBoundBody_model e
end DiophantineConsistency.PRANegExtWitnessBound
