import PA194BothBranchesSentence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SelectedInputFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode ConfigurationStep PRAExhaustion PRAModelIOpenPairing
open PA194BothBranchesSentence PA194StartupSentence PA194RegisterPermutation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local notation "F" => Structure.func (L := language)

def realArgs (e : Fin 12 → M) : Fin 11 → M := fun i => e i.succ
def zeroArgs (e : Fin 12 → M) : Fin 11 → M := fun i => Semiterm.val e Empty.elim (PA194ZeroBranchSentence.args i)
def posArgs (e : Fin 12 → M) : Fin 11 → M :=
  fun i => Semiterm.val (fun j => Semiterm.val e Empty.elim (sub j)) Empty.elim (PA194PositiveBranchSentence.args i)

theorem zeroArgs_eq (e : Fin 12 → M) (hz : e 9 = (0 : M)) : zeroArgs e = realArgs e := by
  funext i
  fin_cases i <;> simp [zeroArgs,realArgs,PA194ZeroBranchSentence.args,valZero,Semiterm.val_bvar,hz]

theorem posArgs_eq (e : Fin 12 → M)
    (hp : F Code.succ (fun _ => F predCode (fun _ => e 9)) = e 9) : posArgs e = realArgs e := by
  have hp' : F addCode ![F predCode (fun _ => e 9), (1 : M)] = e 9 := by
    change F addCode ![F predCode (fun _ => e 9), F oneCode Fin.elim0] = e 9
    rw [modelAddOne]
    exact hp
  funext i
  fin_cases i <;> simp [posArgs,realArgs,PA194PositiveBranchSentence.args,PA194BothBranchesSentence.sub,predTerm,test,
    valApp1,valApp2,valOne,Semiterm.val_bvar,Function.update, hp']

theorem selectedFile (e : Fin 12 → M) :
    F selectCode ![e 9,F sourceFileCode (posArgs e),F sourceFileCode (zeroArgs e)] =
      F sourceFileCode (realArgs e) := by
  classical
  rw [modelSelectAll]
  split
  · rename_i h
    have hz : e 9 = (0 : M) := h
    rw [zeroArgs_eq e hz]
  · rename_i h
    have hp := (modelZeroOrSuccPred (e 9)).resolve_left h
    rw [posArgs_eq e hp]
#print axioms zeroArgs_eq
#print axioms posArgs_eq
#print axioms selectedFile
end models
end PA194SelectedInputFile
