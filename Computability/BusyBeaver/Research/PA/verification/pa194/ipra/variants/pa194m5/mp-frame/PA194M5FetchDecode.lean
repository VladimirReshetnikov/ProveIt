import PA194M5FetchPrefix
import PA194M5FetchReader
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5FetchDecode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ModelMPDrain PA194PausedReach PA194PausedDrain
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def freshFile (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update a 0 (a 0+1)) 8 (a 0)

theorem fresh (a : Fin 11 → M) (tail : M) (h0 : a 8 = 0) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 25 a tail)
      (sourceState 48 (PA194M5FetchReader.output (freshFile a)) tail) := by
  have hp := PA194M5FetchPrefix.fresh a tail h0
  dsimp only at hp
  have heq : (let b := argsAfter a 0 [8,6] (a 0)
    Function.update (Function.update b 0 (b 0+b 6+1)) 6 0) = freshFile a := by
    funext i
    fin_cases i <;> simp [freshFile,argsAfter,location,tally,subSelf,h0,hx,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [heq] at hp
  have hx' : freshFile a 6 = 0 := by simpa [freshFile] using hx
  have hy' : freshFile a 7 = 0 := by simpa [freshFile] using hy
  exact PA194PausedReach.append _ hp (PA194M5FetchReader.reader (freshFile a) tail hx' hy')

theorem positive (a : Fin 11 → M) (tail m : M) (h : a 8 = m+1) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 25 a tail)
      (sourceState 48 (PA194M5FetchReader.output (Function.update a 8 m)) tail) := by
  have hx' : (Function.update a 8 m) 6 = 0 := by simpa using hx
  have hy' : (Function.update a 8 m) 7 = 0 := by simpa using hy
  exact PA194PausedReach.append _ (PA194M5FetchPrefix.positive a tail m h)
    (PA194M5FetchReader.reader (Function.update a 8 m) tail hx' hy')
#print axioms fresh
#print axioms positive
end models
end PA194M5FetchDecode
