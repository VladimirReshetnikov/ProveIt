import PA194SelectedInputFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194UnifiedSourceStepSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194StartupSentence PA194BothBranchesSentence PA194SelectedInputFrame
abbrev T := TermN 12
/-- A single unchanged path-25 input, with clock and output selected by register 8. -/
def lhs : T := app2 PA194Stepper.stepper
  (choose test positiveClock PA194ZeroBranchSentence.clock) canonicalInput
def rhs : T := PA194BothBranchesSentence.rhs
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  have h := ((eqClosureModels _ _).mp (PA194BothBranchesSentence.modelSentence (M := M))) e
  simp only [lhs,rhs,PA194BothBranchesSentence.lhs,valApp2] at h ⊢
  rw [selectedInput_eq] at h
  exact h
end models

theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence

theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194UnifiedSourceStepSentence
