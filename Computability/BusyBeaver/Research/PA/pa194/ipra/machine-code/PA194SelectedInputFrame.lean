import PA194SelectedInputFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SelectedInputFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode ConfigurationStep PRAExhaustion PRAModelIOpenPairing
open PA194BothBranchesSentence PA194StartupSentence PA194RegisterPermutation
open PA194SelectedInputFile PA194Path25Input
abbrev T := TermN 12
def originalArgs : Fin 11 → T := fun i => .bvar i.succ
def originalFile : T := .func sourceFileCode originalArgs
def canonicalRight : T := PA194PositiveBranchSentence.wordTerm (PA194SourceProgram.path 25)
  (app2 PA194ZeroRuns.zeros
    (PA194PositiveBranchSentence.succT (PA194PositiveBranchSentence.succT PA194PositiveBranchSentence.k))
    (PA194PositiveBranchSentence.A PA194PositiveBranchSentence.oneT
      (PA194PositiveBranchSentence.A originalFile originalFile)))
def canonicalInput : T := PA194StartupSentence.pack (PA194PositiveBranchSentence.c 24)
  PA194PositiveBranchSentence.oneT canonicalRight
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem zeroInput_eq (e : Fin 12 → M) (hz : e 9 = (0 : M)) :
    Semiterm.val e Empty.elim zeroInput = Semiterm.val e Empty.elim canonicalInput := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have he := zeroArgs_eq e hz
  have hf := site25Input (M := M) (e 0) (F sourceFileCode (realArgs e))
  dsimp only at hf
  simp only [zeroInput,canonicalInput,canonicalRight,PA194StartupSentence.pack,
    PA194ZeroBranchSentence.c,PA194ZeroBranchSentence.oneT,
    PA194PositiveBranchSentence.c,PA194PositiveBranchSentence.oneT,
    PA194ZeroBranchSentence.inputRight,PA194ZeroBranchSentence.succT,PA194ZeroBranchSentence.A,
    PA194PositiveBranchSentence.succT,PA194PositiveBranchSentence.A,
    PA194ZeroBranchSentence.twiceIter,PA194ZeroBranchSentence.times2,
    PA194ZeroBranchSentence.k,PA194PositiveBranchSentence.k,
    PA194PositiveBranchSentence.valWord,valApp2,valApp1,valState,valOne,modelDoubleCode,
    PA194ZeroBranchSentence.f,originalFile,Semiterm.val_func,Function.comp_def,
    originalArgs,Semiterm.val_bvar]
  change _
  rw [show (fun i => Semiterm.val e Empty.elim (PA194ZeroBranchSentence.args i)) = realArgs e from he]
  exact congrArg (fun t : M => F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![(1 : M),t]]) hf

theorem positiveInput_eq (e : Fin 12 → M)
    (hp : F Code.succ (fun _ => F predCode (fun _ => e 9)) = e 9) :
    Semiterm.val e Empty.elim positiveInput = Semiterm.val e Empty.elim canonicalInput := by
  have he := posArgs_eq e hp
  simp only [positiveInput,Semiterm.val_substs,Function.comp_def,
    PA194StartupSentence.pack,PA194PositiveBranchSentence.inputRight,
    PA194PositiveBranchSentence.c,PA194PositiveBranchSentence.oneT,
    PA194PositiveBranchSentence.succT,PA194PositiveBranchSentence.A,
    PA194PositiveBranchSentence.k,PA194PositiveBranchSentence.f,
    PA194PositiveBranchSentence.valWord,valApp2,valState,valOne,
    canonicalInput,canonicalRight,originalFile,Semiterm.val_func,originalArgs,
    Semiterm.val_bvar]
  rw [show (fun i => Semiterm.val (fun j => Semiterm.val e Empty.elim (sub j)) Empty.elim (PA194PositiveBranchSentence.args i)) = realArgs e from he]
  rfl

theorem selectedInput_eq (e : Fin 12 → M) :
    Semiterm.val e Empty.elim (choose test positiveInput zeroInput) =
      Semiterm.val e Empty.elim canonicalInput := by
  classical
  rw [valChoose]
  simp only [test,Semiterm.val_bvar,modelSelectAll]
  split
  · exact zeroInput_eq e (by assumption)
  · exact positiveInput_eq e ((modelZeroOrSuccPred (e 9)).resolve_left (by assumption))
#print axioms zeroInput_eq
#print axioms positiveInput_eq
#print axioms selectedInput_eq
end models
end PA194SelectedInputFrame
