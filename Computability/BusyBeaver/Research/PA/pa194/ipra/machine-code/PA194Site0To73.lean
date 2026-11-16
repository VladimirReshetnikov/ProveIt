import PA194Site0Prefix
import PA194SourceSite35Physical
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site0To73
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing

theorem path0 : PA194SourceProgram.path 0 = [false,false,false,false,false,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to73 (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let right := F zeros ![gap,(1 : M)+(f+f)]
    F PA194Stepper.stepper ![modelNumeral M 6,PA194SourceSite31Physical.physicalFrame 0 gap args] =
      F pairCode ![modelNumeral M 73,F pairCode ![modelNumeral M 64,right]] := by
  dsimp only
  let f := F sourceFileCode args
  let right := F zeros ![gap,(1 : M)+(f+f)]
  have h := PA194Site0Prefix.prefixWord right
  simp only [modelWord,modelNumeralOne] at h
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [path0]
  exact h
#print axioms path0
#print axioms to73
end models
end PA194Site0To73
