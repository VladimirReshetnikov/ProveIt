import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRALenbitWitnessBound
/-! A local bound for negative Foundation pow2Def, occurring in
    bounded-universal antecedents in sppow2Def and exponentialDef. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegPow2WitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_pow2_bound (a : V) : (∼pow2Def.val).Evalb ![a] →
      (bnd (∼pow2Def.val)).Evalb ![a,a+1] := by
  intro h
  simp [pow2Def, dvd, Semiformula.ballLTSucc, Semiformula.ballLT, Semiformula.bexsLTSucc,
    Semiformula.bexsLT, FirstOrder.ball, FirstOrder.bexs, bnd, bnd_open,
    Rew.subst, Rew.q] at h ⊢
  rcases h with h | ⟨x,hx,hx1,z,hz,haz,hn⟩
  · exact Or.inl h
  · right
    refine ⟨x,hx,?_⟩
    change (bnd _).Evalb ![x,a,a+1]
    simp [DeMorgan.imply, bnd, bnd_open]
    refine ⟨hx,hx1,⟨z,hz,haz⟩,?_⟩
    intro u
    by_cases hu : u < x+1
    · exact Or.inr (hn u hu)
    · exact Or.inl (le_of_not_gt hu)
def negPow2 : ArithmeticSemisentence 1 := ∼pow2Def.val

def boundedNegPow2 : ArithmeticSemisentence 2 := bnd negPow2

def negPow2BoundBody : ArithmeticSemisentence 1 := “a. !negPow2 a → !boundedNegPow2 a (a+1)”

theorem negPow2BoundBody_model (e : Fin 1 → V) : negPow2BoundBody.Eval e Empty.elim := by
  simp [negPow2BoundBody, negPow2, boundedNegPow2, Semiformula.eval_substs]
  intro h
  apply neg_pow2_bound (e 0)
  simpa using h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negPow2BoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negPow2BoundBody

theorem candidate_proves_negPow2_bound : PRA ⊢ negPow2BoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negPow2BoundBody_model e
end DiophantineConsistency.PRANegPow2WitnessBound
