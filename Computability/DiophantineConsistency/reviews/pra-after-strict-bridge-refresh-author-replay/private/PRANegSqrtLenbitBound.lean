import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegLenbitRewritingBound
import DiophantineConsistency.PRAExtWitnessBound
import Foundation.FirstOrder.Arithmetic.Exponential.PPow2
/-! Bound the negative square-root/lenbit existential occurring in
    Foundation sppow2Def. Other sppow2Def conjuncts remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRANegSqrtLenbitBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
def negSqrtLenbit : ArithmeticSemisentence 2 :=
  “x m. ¬∃ s <⁺ x, !sqrtDef s x ∧ s*s = x ∧ !lenbitDef s m”
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem negSqrtLenbit_bound (x m : V) :
    negSqrtLenbit.Evalb ![x,m] →
      (bnd negSqrtLenbit).Evalb ![x,m,m+1] := by
  intro h
  simp [negSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open] at h ⊢
  intro s
  rcases h s with hs | hsqrt | hsq | hlen
  · exact Or.inl hs
  · right; left
    let φ : ArithmeticSemisentence 3 := ∼(Rew.subst (![#0,#1] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ sqrtDef.val)
    have hf : φ.Evalb ![s,x,m] := by simpa [φ, Semiformula.eval_substs] using hsqrt
    have ho : φ.Open := by simp [φ, sqrtDef, Rew.subst]
    exact (PRAExtWitnessBound.eval_open_bnd φ ho ![s,x,m] (m+1)).mpr hf
  · exact Or.inr (Or.inr (Or.inl hsq))
  · right; right; right
    let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
    have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![s,x,m] := by simpa [ω, Semiformula.eval_substs] using hlen
    have hb := PRANegLenbitRewritingBound.neg_lenbit_rew_bound ω ![s,x,m] hf
    exact hb
def boundedNegSqrtLenbit : ArithmeticSemisentence 3 := bnd negSqrtLenbit

def negSqrtLenbitBoundBody : ArithmeticSemisentence 2 :=
  “x m. !negSqrtLenbit x m → !boundedNegSqrtLenbit x m (m+1)”

theorem negSqrtLenbitBoundBody_model (e : Fin 2 → V) : negSqrtLenbitBoundBody.Eval e Empty.elim := by
  simp [negSqrtLenbitBoundBody, boundedNegSqrtLenbit, Semiformula.eval_substs]
  exact negSqrtLenbit_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negSqrtLenbitBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negSqrtLenbitBoundBody

theorem candidate_proves_negSqrtLenbit_bound : PRA ⊢ negSqrtLenbitBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negSqrtLenbitBoundBody_model e
end DiophantineConsistency.PRANegSqrtLenbitBound
