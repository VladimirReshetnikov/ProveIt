import PA194UnifiedOutputSpec
import PA194OpenFormulaTransfer
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194PositiveBranchImplication
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
def updatedOriginalArgs : Fin 11 → T := Function.update originalArgs 8 predTerm
def updatedOriginalFile : T := .func sourceFileCode updatedOriginalArgs
def positiveTarget : T := PA194StartupSentence.pack (PA194PositiveBranchSentence.c 24)
  PA194PositiveBranchSentence.oneT
  (PA194PositiveBranchSentence.wordTerm (PA194SourceProgram.path 26)
    (app2 PA194ZeroRuns.zeros
      (PA194PositiveBranchSentence.succT (PA194PositiveBranchSentence.succT (PA194PositiveBranchSentence.succT PA194PositiveBranchSentence.k)))
      (PA194PositiveBranchSentence.A PA194PositiveBranchSentence.oneT
        (PA194PositiveBranchSentence.A updatedOriginalFile updatedOriginalFile))))
def matrix : Semisentence language 12 :=
  .rel Language.ORing.Rel.eq ![test,zero] ⋎
    .rel Language.ORing.Rel.eq ![PA194UnifiedSourceStepSentence.lhs,positiveTarget]
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
  · exact Or.inl hz
  · apply Or.inr
    have hu := ((eqClosureModels _ _).mp (PA194UnifiedSourceStepSentence.modelSentence (M := M))) e
    have ho := selectedOutput e
    simp only [hz,if_false] at ho
    have hv : (fun i => Semiterm.val e Empty.elim (updatedOriginalArgs i)) =
        Function.update (realArgs e) 8 (F predCode (fun _ => e 9)) := by
      funext i
      by_cases hi : i = 8
      · subst i; simp [updatedOriginalArgs,realArgs,predTerm,test,valApp1,Semiterm.val_bvar]
      · simp [updatedOriginalArgs,realArgs,originalArgs,Function.update_of_ne hi,Semiterm.val_bvar]
    have ht : Semiterm.val e Empty.elim positiveTarget =
        F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),
          PA194Path27Header.modelWord (PA194SourceProgram.path 26)
            (F PA194ZeroRuns.zeros ![((e 0+1)+1)+1,1+
              (F sourceFileCode (Function.update (realArgs e) 8 (F predCode (fun _ => e 9)))+
               F sourceFileCode (Function.update (realArgs e) 8 (F predCode (fun _ => e 9))))])]] := by
      simp only [positiveTarget,PA194StartupSentence.pack,PA194PositiveBranchSentence.c,
        PA194PositiveBranchSentence.oneT,PA194PositiveBranchSentence.succT,PA194PositiveBranchSentence.A,
        PA194PositiveBranchSentence.k,updatedOriginalFile,
        PA194PositiveBranchSentence.valWord,valApp2,valState,valOne,Semiterm.val_bvar,
        Semiterm.val_func,Function.comp_def]
      rw [hv]
      rfl
    exact hu.trans (ho.trans ht.symm)

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
def outputEq : Semisentenceᵢ language 12 := .rel Language.ORing.Rel.eq ![PA194UnifiedSourceStepSentence.lhs,positiveTarget]
def implication : Sentenceᵢ language := ∀⁰* (∼testEq 🡒 outputEq)

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

theorem nativeImplication : standardTheory ⊢ implication := by
  have hn : nativeTheory ⊢! ∀⁰* native matrix :=
    Classical.choice ((IPRAStandardTheory.provable_iff _).1 nativeDisjunction)
  apply (IPRAStandardTheory.provable_iff _).2
  apply Nonempty.intro
  change nativeTheory ⊢! ∀⁰* (∼testEq 🡒 outputEq)
  apply IPRANativeDisjunctionWitness.closeFamily 12 (∼testEq 🡒 outputEq)
  intro v
  have hinst := IPRATheoryInstantiation.instantiateTheory (T := nativeTheory) (native matrix) hn v
  have hdisj : extended nativeTheory ⊢! (Rew.embSubsts v ▹ testEq) ⋎ (Rew.embSubsts v ▹ outputEq) := by
    simpa [matrix,testEq,outputEq,IPRANativeFormula.native] using hinst
  have hdisj' : extended nativeTheory ⊢! ∼∼(Rew.embSubsts v ▹ testEq) ⋎ (Rew.embSubsts v ▹ outputEq) :=
    Entailment.left_A_intro (Entailment.C_trans Entailment.dni Entailment.or₁) Entailment.or₂ ⨀ hdisj
  have himp := Entailment.C_of_AN hdisj'
  simpa only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using himp
#print axioms nativeImplication
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeDisjunction
end PA194PositiveBranchImplication
