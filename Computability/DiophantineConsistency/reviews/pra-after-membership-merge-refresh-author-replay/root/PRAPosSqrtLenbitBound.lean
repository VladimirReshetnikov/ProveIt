import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRABndRewriting
import DiophantineConsistency.PRAExtWitnessBound
import Foundation.FirstOrder.Arithmetic.Exponential.PPow2
/-! Bound the positive sqrt/lenbit existential in sppow2Def when
    the index is at most the outer argument. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAPosSqrtLenbitBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
def posSqrtLenbit : ArithmeticSemisentence 2 :=
  “x m. ∃ s <⁺ x, !sqrtDef s x ∧ s*s = x ∧ !lenbitDef s m”
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem posSqrtLenbit_bound (x m : V) (hxm : x ≤ m) :
    posSqrtLenbit.Evalb ![x,m] →
      (bnd posSqrtLenbit).Evalb ![x,m,m+1] := by
  intro h
  simp [posSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open] at h ⊢
  have hsm : √x < m+1 := lt_of_lt_of_le h.1 (by simpa [add_comm] using add_le_add_right hxm 1)
  refine ⟨√x,hsm,h.1,?_,h.2.1,?_⟩
  · let φ : ArithmeticSemisentence 3 := Rew.subst (![#0,#1] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ sqrtDef.val
    have hf : φ.Evalb ![√x,x,m] := by simp [φ, Semiformula.eval_substs]
    have ho : φ.Open := by simp [φ, sqrtDef, Rew.subst]
    exact (PRAExtWitnessBound.eval_open_bnd φ ho ![√x,x,m] (m+1)).mpr hf
  · let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
    have hf : lenbitDef.val.Evalb ![√x,m] := by simpa using h.2.2
    have hb := PRALenbitWitnessBound.lenbit_bound (√x) m hf
    have hn := PRABndRewriting.natural lenbitDef.val ω ![√x,x,m] (m+1)
    exact hn.mpr hb
def boundedPosSqrtLenbit : ArithmeticSemisentence 3 := bnd posSqrtLenbit

def posSqrtLenbitBoundBody : ArithmeticSemisentence 2 :=
  “x m. x ≤ m ∧ !posSqrtLenbit x m → !boundedPosSqrtLenbit x m (m+1)”

theorem posSqrtLenbitBoundBody_model (e : Fin 2 → V) : posSqrtLenbitBoundBody.Eval e Empty.elim := by
  simp [posSqrtLenbitBoundBody, boundedPosSqrtLenbit, Semiformula.eval_substs]
  intro h₁ h₂
  apply posSqrtLenbit_bound (e 0) (e 1) (by simpa using h₁)
  exact h₂
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def posSqrtLenbitBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding posSqrtLenbitBoundBody

theorem candidate_proves_posSqrtLenbit_bound : PRA ⊢ posSqrtLenbitBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact posSqrtLenbitBoundBody_model e
end DiophantineConsistency.PRAPosSqrtLenbitBound
