import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAExtWitnessBound
import DiophantineConsistency.PRARewritingWitnessBound
/-! Transfer the extDef local bound through arbitrary substitutions, including
    the exact first initial occurrence in exponentialDef. The remainder of
    exponentialDef is not bounded here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAExtRewritingBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAExtWitnessBound DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem ext_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) :
    (ω ▹ extDef.val).Evalb e →
      (bnd (ω ▹ extDef.val)).Evalb (Fin.snoc e (((ω #2).val e Empty.elim)+1)) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact PRARewritingWitnessBound.ternary_rew_bound_with extDef.val (fun _ _ z => z+1)
    ext_bound ω e _ le_rfl

def initialX : ArithmeticSemisentence 1 := “X. !extDef 1 4 X”

theorem initialX_bound (X : V) (h : initialX.Evalb ![X]) :
    (bnd initialX).Evalb ![X,X+1] :=
  ext_rew_bound (Rew.subst ![Semiterm.numeral 1,Semiterm.numeral 4,#0]) ![X] h
def boundedInitialX : ArithmeticSemisentence 2 := bnd initialX

def initialXBoundBody : ArithmeticSemisentence 1 := “X. !initialX X → !boundedInitialX X (X+1)”

theorem initialXBoundBody_model (e : Fin 1 → V) : initialXBoundBody.Eval e Empty.elim := by
  simp [initialXBoundBody, boundedInitialX, Semiformula.eval_substs]
  exact initialX_bound (e 0)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def initialXBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding initialXBoundBody

theorem candidate_proves_initialX_bound : PRA ⊢ initialXBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact initialXBoundBody_model e
end DiophantineConsistency.PRAExtRewritingBound
