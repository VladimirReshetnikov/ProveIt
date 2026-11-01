import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRANegLenbitWitnessBound
/-! Bound the rewritten negative lenbit graph, including the first
    concrete occurrence in Foundation sppow2Def. This is a local result. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegLenbitRewritingBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRANegLenbitWitnessBound DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_lenbit_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 2 Empty n) (e : Fin n → V) :
    (ω ▹ (∼lenbitDef.val)).Evalb e →
      (bnd (ω ▹ (∼lenbitDef.val))).Evalb (Fin.snoc e (((ω #1).val e Empty.elim)+1)) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact PRARewritingWitnessBound.binary_rew_bound_with (∼lenbitDef.val) (fun _ y => y+1)
    PRANegLenbitWitnessBound.neg_lenbit_bound ω e _ le_rfl

def negFirst : ArithmeticSemisentence 1 := “m. ¬!lenbitDef 1 m”
theorem negFirst_bound (m : V) (h : negFirst.Evalb ![m]) :
    (bnd negFirst).Evalb ![m,m+1] :=
  neg_lenbit_rew_bound (Rew.subst ![Semiterm.numeral 1,#0]) ![m] h
def boundedNegFirst : ArithmeticSemisentence 2 := bnd negFirst

def negFirstBoundBody : ArithmeticSemisentence 1 := “m. !negFirst m → !boundedNegFirst m (m+1)”

theorem negFirstBoundBody_model (e : Fin 1 → V) : negFirstBoundBody.Eval e Empty.elim := by
  simp [negFirstBoundBody, boundedNegFirst, Semiformula.eval_substs]
  exact negFirst_bound (e 0)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negFirstBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negFirstBoundBody

theorem candidate_proves_negFirst_bound : PRA ⊢ negFirstBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negFirstBoundBody_model e
end DiophantineConsistency.PRANegLenbitRewritingBound
