import PA194ZeroBranchSentence
import PA194PositiveBranchSentence
import ConfigurationStep
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194BothBranchesSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRASelectCode ConfigurationStep PA194StartupSentence
abbrev T := TermN 12

def test : T := .bvar 9
def predTerm : T := app1 predCode test
/-- Replace positive branch's m by the predecessor of the original tested register. -/
def sub : Fin 12 → T := Function.update (fun i => .bvar i) 9 predTerm
def choose (v yes no : T) : T := .func selectCode ![v,yes,no]
def positiveClock : T := Rew.subst sub PA194PositiveBranchSentence.clock
def positiveInput : T := Rew.subst sub
  (PA194StartupSentence.pack (PA194PositiveBranchSentence.c 24)
    PA194PositiveBranchSentence.oneT PA194PositiveBranchSentence.inputRight)
def positiveOutput : T := Rew.subst sub PA194PositiveBranchSentence.rhs
def zeroInput : T := PA194StartupSentence.pack (PA194ZeroBranchSentence.c 24)
  PA194ZeroBranchSentence.oneT PA194ZeroBranchSentence.inputRight
def lhs : T := app2 PA194Stepper.stepper
  (choose test positiveClock PA194ZeroBranchSentence.clock)
  (choose test positiveInput zeroInput)
def rhs : T := choose test positiveOutput PA194ZeroBranchSentence.rhs
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valChoose (e : Fin 12 → M) (v a b : T) :
  Semiterm.val e Empty.elim (choose v a b) =
    F selectCode ![Semiterm.val e Empty.elim v,Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [choose,Semiterm.val_func]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun j => ?_) j
  exact Fin.cases rfl (fun j => Fin.elim0 j) j

theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  apply (eqClosureModels _ _).mpr
  intro e
  let ep : Fin 12 → M := fun i => Semiterm.val e Empty.elim (sub i)
  have hz := ((eqClosureModels _ _).mp (PA194ZeroBranchSentence.modelSentence (M := M))) e
  have hp := ((eqClosureModels _ _).mp (PA194PositiveBranchSentence.modelSentence (M := M))) ep
  simp only [lhs,rhs,valApp2,valChoose,test,Semiterm.val_bvar,modelSelectAll]
  split
  · simpa only [PA194ZeroBranchSentence.lhs,valApp2,zeroInput] using hz
  · simpa only [positiveClock,positiveInput,positiveOutput,Semiterm.val_substs,
      Function.comp_def,PA194PositiveBranchSentence.lhs,valApp2,ep] using hp
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
end PA194BothBranchesSentence
