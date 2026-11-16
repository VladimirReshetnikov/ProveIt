import PA194Site3672JumpRows
import PA194Site32ZeroPath
import PA194Path34Header
import PA194Path31Header
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site3672JumpPath
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194BinaryDouble PA194Site32ZeroPath PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem path3672 : PA194SourceProgram.path 3672 = [true,true,true] := by decide +kernel

theorem path0 : PA194SourceProgram.path 0 = [false,false,false,false,false,false] := by decide +kernel

theorem jumpPath (k : M) (args : Fin 11 → M) :
    F PA194Stepper.stepper ![modelNumeral M 24,PA194SourceSite31Physical.physicalFrame 3672 (((k+1)+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 0 k args := by
  let f := F sourceFileCode args
  let base := (1 : M)+(f+f)
  let z := F zeros ![k,base]
  have hi : modelWord (PA194SourceProgram.path 3672) (F zeros ![(((k+1)+1)+1),base]) =
      modelWord [true,true,true] (F zeros ![(((k+1)+1)+1),base]) := by rw [path3672]
  have ho : modelWord (PA194SourceProgram.path 0) (F zeros ![k,base]) =
      modelWord [false,false,false] (F zeros ![(((k+1)+1)+1),base]) := by
    rw [path0,zerosSucc,zerosSucc,zerosSucc]
    rfl
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [hi,ho]
  have h := PA194Site3672JumpRows.prefixWord (F zeros ![(((k+1)+1)+1),base])
  rw [modelNumeralOne] at h
  exact h
#print axioms path3672
#print axioms path0
#print axioms jumpPath
end models
end PA194Site3672JumpPath
