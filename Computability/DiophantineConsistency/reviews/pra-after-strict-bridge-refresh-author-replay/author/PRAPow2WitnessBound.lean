import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAExtWitnessBound
/-! A local bound for Foundation pow2Def, using IOpen rather than
    bounded collection. This does not bound ppow2Def or exponentialDef. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAPow2WitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem pow2_bound (a : V) : pow2Def.val.Evalb ![a] →
      (bnd pow2Def.val).Evalb ![a,a+1] := by
  intro h
  simp [pow2Def, dvd, Semiformula.ballLTSucc, Semiformula.ballLT, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.ball, FirstOrder.bexs, Semiformula.neg, bnd, bnd_open, Rew.subst, Rew.q] at h ⊢
  constructor
  · exact h.1
  · intro x
    by_cases hx : x < a+1
    · by_cases hx1 : 1 < x
      · by_cases hw : ∃ z < a+1, a = x*z
        · rcases hw with ⟨z,hz,hza⟩
          rcases h.2 x hx hx1 z hz hza with ⟨u,hu,huEq⟩
          right; right; right
          have hxa : x ≤ a := lt_succ_iff_le.mp hx
          exact ⟨u, lt_of_lt_of_le hu (by simpa [add_comm] using add_le_add_right hxa 1), hu, huEq⟩
        · right; right; left
          intro z
          by_cases hz : z < a+1
          · right
            have hneq : a ≠ x*z := fun he => hw ⟨z,hz,he⟩
            have ho : (∼ (“#2 = #1 * #0” : ArithmeticSemisentence 3)).Evalb ![z,x,a] := by simpa using hneq
            have he := (PRAExtWitnessBound.eval_open_bnd (∼ (“#2 = #1 * #0” : ArithmeticSemisentence 3)) (by simp) ![z,x,a] (a+1)).mpr ho
            exact he
          · left
            have ho : (∼ (“#0 < #2 + 1” : ArithmeticSemisentence 3)).Evalb ![z,x,a] := by simpa using hz
            have he := (PRAExtWitnessBound.eval_open_bnd (∼ (“#0 < #2 + 1” : ArithmeticSemisentence 3)) (by simp) ![z,x,a] (a+1)).mpr ho
            exact he
      · right; left
        have ho : (∼ (“1 < #0” : ArithmeticSemisentence 2)).Evalb ![x,a] := by simpa using hx1
        have he := (PRAExtWitnessBound.eval_open_bnd (∼ (“1 < #0” : ArithmeticSemisentence 2)) (by simp) ![x,a] (a+1)).mpr ho
        exact he
    · left
      have ho : (∼ (“#0 < #1 + 1” : ArithmeticSemisentence 2)).Evalb ![x,a] := by simpa using hx
      have he := (PRAExtWitnessBound.eval_open_bnd (∼ (“#0 < #1 + 1” : ArithmeticSemisentence 2)) (by simp) ![x,a] (a+1)).mpr ho
      exact he
def boundedPow2 : ArithmeticSemisentence 2 := bnd pow2Def.val

def pow2BoundBody : ArithmeticSemisentence 1 := “a. !pow2Def a → !boundedPow2 a (a+1)”

theorem pow2BoundBody_model (e : Fin 1 → V) : pow2BoundBody.Eval e Empty.elim := by
  simp [pow2BoundBody, boundedPow2, Semiformula.eval_substs]
  intro h
  apply pow2_bound (e 0)
  simpa using h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def pow2BoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding pow2BoundBody

theorem candidate_proves_pow2_bound : PRA ⊢ pow2BoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact pow2BoundBody_model e
end DiophantineConsistency.PRAPow2WitnessBound
