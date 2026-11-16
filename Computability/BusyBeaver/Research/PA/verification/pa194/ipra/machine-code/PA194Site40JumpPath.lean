import PA194Site40Jump
import PA194Site38To30
import PA194Path31Header
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site40JumpPath
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

theorem jumpPath (k : M) (args : Fin 11 → M) :
    F PA194Stepper.stepper ![modelNumeral M 40,PA194SourceSite31Physical.physicalFrame 40 k args] =
      PA194SourceSite31Physical.physicalFrame 38 (k+1) args := by
  let f := F sourceFileCode args
  let base := (1 : M)+(f+f)
  let z := F zeros ![k,base]
  have hi : modelWord (PA194SourceProgram.path 40) (F zeros ![k,base]) =
      modelWord [true,false,false,true,false,false,true,true,false,true,true,true] z := by
    rw [show PA194SourceProgram.path 40 = [true,false,false,true,false,false,true,true,false,true,true,true] by decide +kernel]
  have ho : modelWord (PA194SourceProgram.path 38) (F zeros ![k+1,base]) =
      modelWord [true,false,false,true,false,false,true,true,false,true,false,false] z := by
    rw [zerosSucc,PA194Site38To30.path38]
    rfl
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [hi,ho]
  have h := PA194Site40Jump.jumpWord z
  rw [modelNumeralOne] at h
  exact h
#print axioms jumpPath
end models
end PA194Site40JumpPath
