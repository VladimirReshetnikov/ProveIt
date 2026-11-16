import PA194UnifiedSourceStepSentence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194UnifiedOutputSpec
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode ConfigurationStep PRAExhaustion PRAModelIOpenPairing
open PA194StartupSentence PA194BothBranchesSentence PA194RegisterPermutation
open PA194SelectedInputFile PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : DecidableEq M := Classical.decEq M
local notation "F" => Structure.func (L := language)

theorem zeroOutputWord (k f : M) :
    let y := F PA194ZeroRuns.zeros ![k+1,f+f+1]
    let y1 := y+y
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let y7 := y6+y6
    let o2 := (1 : M)+1
    let o4 := o2+o2
    let o8 := o4+o4
    let o16 := o8+o8
    y7+o16+1 = modelWord (PA194SourceProgram.path 27)
      (F PA194ZeroRuns.zeros ![k+1,1+(f+f)]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have harg : (1 : M)+(f+f)=f+f+1 := by simp only [add_comm]
  rw [harg,path27]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte]
  simp only [add_assoc,add_comm,add_left_comm]
theorem zeroOutput (e : Fin 12 → M) (hz : e 9 = (0 : M)) :
    Semiterm.val e Empty.elim PA194ZeroBranchSentence.rhs =
      F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),
        modelWord (PA194SourceProgram.path 27)
          (F PA194ZeroRuns.zeros ![e 0+1,1+(F sourceFileCode (realArgs e)+F sourceFileCode (realArgs e))])]] := by
  have he := zeroArgs_eq e hz
  have hw := zeroOutputWord (M := M) (e 0) (F sourceFileCode (realArgs e))
  dsimp only at hw
  simp only [PA194ZeroBranchSentence.rhs,PA194StartupSentence.pack,
    PA194ZeroBranchSentence.outputRight,PA194ZeroBranchSentence.A,
    PA194ZeroBranchSentence.oneT,PA194ZeroBranchSentence.c,PA194ZeroBranchSentence.succT,
    PA194ZeroBranchSentence.twiceIter,PA194ZeroBranchSentence.times2,
    PA194ZeroBranchSentence.k,PA194ZeroBranchSentence.f,
    valApp2,valApp1,valState,valOne,modelDoubleCode,Semiterm.val_bvar,
    Semiterm.val_func,Function.comp_def]
  rw [show (fun i => Semiterm.val e Empty.elim (PA194ZeroBranchSentence.args i)) = realArgs e from he]
  exact congrArg (fun t : M => F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),t]]) hw

theorem positiveOutput (e : Fin 12 → M)
    (hp : F Code.succ (fun _ => F predCode (fun _ => e 9)) = e 9) :
    Semiterm.val e Empty.elim PA194BothBranchesSentence.positiveOutput =
      F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),
        modelWord (PA194SourceProgram.path 26)
          (F PA194ZeroRuns.zeros ![((e 0+1)+1)+1,1+
            (F sourceFileCode (Function.update (realArgs e) 8 (F predCode (fun _ => e 9)) )+
             F sourceFileCode (Function.update (realArgs e) 8 (F predCode (fun _ => e 9))))])]] := by
  classical
  let ep : Fin 12 → M := fun j => Semiterm.val e Empty.elim (PA194BothBranchesSentence.sub j)
  have he := posArgs_eq e hp
  have hpred : ep 9 = F predCode (fun _ => e 9) := by
    simp [ep,PA194BothBranchesSentence.sub,predTerm,test,valApp1,Semiterm.val_bvar]
  have hu : (fun i => Semiterm.val ep Empty.elim (PA194PositiveBranchSentence.updatedArgs i)) =
      Function.update (realArgs e) 8 (F predCode (fun _ => e 9)) := by
    funext i
    by_cases hi : i = 8
    · subst i
      simp [PA194PositiveBranchSentence.updatedArgs,hpred,Function.update]
    · have hi' := congrFun he i
      simp only [posArgs,ep] at hi'
      simp only [PA194PositiveBranchSentence.updatedArgs,Function.update_of_ne hi]
      exact hi'
  simp only [PA194BothBranchesSentence.positiveOutput,Semiterm.val_substs,Function.comp_def,
    PA194PositiveBranchSentence.rhs,PA194StartupSentence.pack,PA194PositiveBranchSentence.outputRight,
    PA194PositiveBranchSentence.c,PA194PositiveBranchSentence.oneT,
    PA194PositiveBranchSentence.A,PA194PositiveBranchSentence.succT,PA194PositiveBranchSentence.k,
    PA194PositiveBranchSentence.fupdated,PA194PositiveBranchSentence.valWord,
    valApp2,valState,valOne,Semiterm.val_bvar,Semiterm.val_func]
  change _
  rw [show (fun i => Semiterm.val ep Empty.elim (PA194PositiveBranchSentence.updatedArgs i)) =
      Function.update (realArgs e) 8 (F predCode (fun _ => e 9)) from hu]
  rfl

theorem selectedOutput (e : Fin 12 → M) :
    Semiterm.val e Empty.elim PA194UnifiedSourceStepSentence.rhs =
      if e 9 = (0 : M) then
        F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),
          modelWord (PA194SourceProgram.path 27)
            (F PA194ZeroRuns.zeros ![e 0+1,1+(F sourceFileCode (realArgs e)+F sourceFileCode (realArgs e))])]]
      else
        F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),
          modelWord (PA194SourceProgram.path 26)
            (F PA194ZeroRuns.zeros ![((e 0+1)+1)+1,1+
              (F sourceFileCode (Function.update (realArgs e) 8 (F predCode (fun _ => e 9)) )+
               F sourceFileCode (Function.update (realArgs e) 8 (F predCode (fun _ => e 9))))])]] := by
  classical
  simp only [PA194UnifiedSourceStepSentence.rhs,PA194BothBranchesSentence.rhs,valChoose,
    test,Semiterm.val_bvar,modelSelectAll]
  change (if e 9 = (0 : M) then Semiterm.val e Empty.elim PA194ZeroBranchSentence.rhs else Semiterm.val e Empty.elim PA194BothBranchesSentence.positiveOutput) = _
  by_cases hz : e 9 = (0 : M)
  · simp only [hz, if_true]
    exact zeroOutput e hz
  · simp only [hz, if_false]
    exact positiveOutput e ((modelZeroOrSuccPred (e 9)).resolve_left hz)
#print axioms zeroOutput
#print axioms positiveOutput
#print axioms selectedOutput
#print axioms zeroOutputWord
end models
end PA194UnifiedOutputSpec
