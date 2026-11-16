import PA194UnifiedOutputSpec
import PA194OpenFormulaTransfer
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194ZeroBranchImplication
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRANativeFormula IPRANativeFormulaRew IPRATheoryHilbertBridge IPRATheoryInstantiation
open Rewriting HilbertProofᵢ
open IPRANativeTheory IPRAStandardTheory IPRAQuantifierFree
open PA194StartupSentence PA194BothBranchesSentence PA194SelectedInputFrame
open PA194UnifiedOutputSpec PA194OpenFormulaTransfer PA194RegisterPermutation PA194SelectedInputFile
abbrev T := TermN 12
def zeroTarget : T := PA194StartupSentence.pack (PA194PositiveBranchSentence.c 24)
  PA194PositiveBranchSentence.oneT
  (PA194PositiveBranchSentence.wordTerm (PA194SourceProgram.path 27)
    (app2 PA194ZeroRuns.zeros (PA194PositiveBranchSentence.succT PA194PositiveBranchSentence.k)
      (PA194PositiveBranchSentence.A PA194PositiveBranchSentence.oneT
        (PA194PositiveBranchSentence.A originalFile originalFile))))
def matrix : Semisentence language 12 :=
  .nrel Language.ORing.Rel.eq ![test,zero] ⋎
    .rel Language.ORing.Rel.eq ![PA194UnifiedSourceStepSentence.lhs,zeroTarget]
def sentence : Sentence language := ∀⁰* matrix
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  simp only [sentence,models_iff,Semiformula.eval_allClosure]
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e matrix
  simp [matrix,Semiformula.EvalAux,eqRel,Function.comp_def,test,valZero,Semiterm.val_bvar]
  by_cases hz : e 9 = (0 : M)
  · apply Or.inr
    have hu := ((eqClosureModels _ _).mp (PA194UnifiedSourceStepSentence.modelSentence (M := M))) e
    have ho := selectedOutput e
    simp only [hz,if_true] at ho
    have ht : Semiterm.val e Empty.elim zeroTarget =
        F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),
          PA194Path27Header.modelWord (PA194SourceProgram.path 27)
            (F PA194ZeroRuns.zeros ![e 0+1,1+(F sourceFileCode (realArgs e)+F sourceFileCode (realArgs e))])]] := by
      simp only [zeroTarget,PA194StartupSentence.pack,PA194PositiveBranchSentence.c,
        PA194PositiveBranchSentence.oneT,PA194PositiveBranchSentence.succT,PA194PositiveBranchSentence.A,
        PA194PositiveBranchSentence.k,originalFile,originalArgs,
        PA194PositiveBranchSentence.valWord,valApp2,valState,valOne,Semiterm.val_bvar,
        Semiterm.val_func,Function.comp_def,realArgs]
      rfl
    exact hu.trans (ho.trans ht.symm)
  · exact Or.inl hz
end models

theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence

theorem nativeDisjunction : standardTheory ⊢ ∀⁰* native matrix := by
  apply nativeOpenOfClassical matrix
  · simp [matrix,Semiformula.Open]
  · exact classicalPRA
def testEq : Semisentenceᵢ language 12 := .rel Language.ORing.Rel.eq ![test,zero]
def outputEq : Semisentenceᵢ language 12 := .rel Language.ORing.Rel.eq ![PA194UnifiedSourceStepSentence.lhs,zeroTarget]
def implication : Sentenceᵢ language := ∀⁰* (testEq 🡒 outputEq)

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

theorem nativeImplication : standardTheory ⊢ implication := by
  have hn : nativeTheory ⊢! ∀⁰* native matrix :=
    Classical.choice ((IPRAStandardTheory.provable_iff _).1 nativeDisjunction)
  apply (IPRAStandardTheory.provable_iff _).2
  apply Nonempty.intro
  change nativeTheory ⊢! ∀⁰* (testEq 🡒 outputEq)
  apply IPRANativeDisjunctionWitness.closeFamily 12 (testEq 🡒 outputEq)
  intro v
  have hinst := IPRATheoryInstantiation.instantiateTheory (T := nativeTheory) (native matrix) hn v
  have hdisj : extended nativeTheory ⊢! ∼(Rew.embSubsts v ▹ testEq) ⋎ (Rew.embSubsts v ▹ outputEq) := by
    simpa [matrix,testEq,outputEq,IPRANativeFormula.native] using hinst
  have himp := Entailment.C_of_AN hdisj
  simpa only [LogicalConnective.HomClass.map_imply] using himp
#print axioms nativeImplication
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeDisjunction
end PA194ZeroBranchImplication
