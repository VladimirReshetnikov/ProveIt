import PA194Site3668Prefix
import PA194SourceSite35Physical
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3668To42
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing

theorem path3668 : PA194SourceProgram.path 3668 = [true,false,true,true,true,true,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to42 (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let right := F zeros ![gap,(1 : M)+(f+f)]
    F PA194Stepper.stepper ![modelNumeral M 7,PA194SourceSite31Physical.physicalFrame 3668 gap args] =
      F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 222,right]] := by
  dsimp only
  let f := F sourceFileCode args
  let right := F zeros ![gap,(1 : M)+(f+f)]
  have h := PA194Site3668Prefix.prefixWord right
  simp only [modelWord,modelNumeralOne] at h
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [path3668]
  exact h
#print axioms path3668
#print axioms to42
end models
end PA194Site3668To42
