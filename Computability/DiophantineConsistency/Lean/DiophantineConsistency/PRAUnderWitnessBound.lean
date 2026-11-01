import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRAExpWitnessBound
/-! Explicit positive bound for the actual Foundation underDef graph. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAUnderWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] expDef

theorem under_bound (y x : V) : underDef.val.Evalb ![y,x] →
    (bnd underDef.val).Evalb ![y,x,PRAExponentialWitnessBound.exponentialMajorant (y+1)] := by
  intro h
  simp [underDef] at h ⊢
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![‘#0+1’,#1]
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hb := PRARewritingWitnessBound.binary_rew_bound_with expDef.val
    (fun y _ => PRAExponentialWitnessBound.exponentialMajorant y)
    PRAExpWitnessBound.exp_bound ω ![y,x]
    (PRAExponentialWitnessBound.exponentialMajorant (y+1)) (by simp [ω])
    (by simpa [ω, Semiformula.eval_substs] using h)
  simpa [ω] using hb
noncomputable def boundedUnder : ArithmeticSemisentence 3 := bnd underDef.val
noncomputable def underBoundBody : ArithmeticSemisentence 2 :=
  “y x. !underDef y x → !boundedUnder y x (((y+1)⁴+1)+((y+1)²+1)+(2*(y+1)²+1)+((y+1)⁴+(y+1)⁴+2*(y+1)+1))”
theorem underBoundBody_model (e : Fin 2 → V) : underBoundBody.Eval e Empty.elim := by
  simp [underBoundBody, boundedUnder, Semiformula.eval_substs]
  exact under_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def underBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding underBoundBody
theorem candidate_proves_under_bound : PRA ⊢ underBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact underBoundBody_model e
end DiophantineConsistency.PRAUnderWitnessBound
