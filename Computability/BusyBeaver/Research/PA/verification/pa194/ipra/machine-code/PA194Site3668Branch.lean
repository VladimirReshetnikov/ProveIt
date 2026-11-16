import PA194Site3668To4
import PA194Site27BranchRows
import PA194Site3668CarryFrom1
import PA194Site3668To1
import PA194Site3668MarkedFile
import PA194Site32CarryTo4
import PA194Site3668SecondPass
import PA194Site3668ThirdPrefix
import PA194Site3668SecondTo17
import PA194Site3668SecondReturn
import PA194Site3668SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site3668Branch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194CarryFile PA194Path27Header PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def runTo4 (k : M) (args : Fin 11 → M) : M :=
    let e := physicalArgs args
    let out := PA194Site3668SecondTo17.output k args
    let v := physicalArgs args
    let sel := PA194Site3668MarkedFile.selectedArgs args
    let tail := F (fileCode 1) (fun i => sel i.succ)
    let q := F ones ![sel 0,tail]
    let vec := PA194Site3668MarkedFile.prefixArgs args
    let before := F ones ![k+1,modelNumeral M 888]
    let left := F (PA194CarryFile.leftCode 8) (Fin.cases before vec)
    let z := left+left+1
    let cost := ((k+1)+F (PA194CarryFile.costCode 8) vec)+modelNumeral M 2
    F PA194Stepper.stepper ![cost,
    F PA194Stepper.stepper ![modelNumeral M 9,
    F PA194Stepper.stepper ![modelNumeral M 24,F PA194Stepper.stepper ![((k+1)+1)+1,
      F PA194Stepper.stepper ![(e 0+1)+1,
        F PA194Stepper.stepper ![(e 1+1)+1,
          F PA194Stepper.stepper ![PA194Site3668SecondTo17.sixCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site3668SecondTo14.clock k args,
                PA194SourceSite31Physical.physicalFrame 3668 ((k+1)+1) args]]]]]]]]]
noncomputable def marker (k : M) (args : Fin 11 → M) : M :=
  let vec := PA194Site3668MarkedFile.prefixArgs args
  let before := F ones ![k+1,modelNumeral M 888]
  let left := F (PA194CarryFile.leftCode 8) (Fin.cases before vec)
  left+left+1
def selectedTail (args : Fin 11 → M) : M :=
  F (fileCode 1) (fun i => (PA194Site3668MarkedFile.selectedArgs args) i.succ)

theorem at4 (k : M) (args : Fin 11 → M) :
    let q := F ones ![args 6,selectedTail args]
    let z := marker k args
    runTo4 k args = F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]] := by
  exact PA194Site3668To4.to4 k args

theorem zeroTo5 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let v := physicalArgs args
    let t := F ones ![v 9+1,v 10]
    let z := marker k args
    F PA194Stepper.stepper ![modelNumeral M 1,runTo4 k args] =
      F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]] := by
  dsimp only
  let v := physicalArgs args
  let t := F ones ![v 9+1,v 10]
  have ht : selectedTail args = t+t := by
    dsimp only [selectedTail,t,PA194Site3668MarkedFile.selectedArgs]
    rw [modelFileSucc,modelBlock]
    simp only [fileCode,modelProjection]
    rfl
  have h := at4 k args
  dsimp only at h
  rw [hz,ht] at h
  rw [h]
  exact PA194Site27BranchRows.zeroRow (marker k args) t

theorem positiveTo6 (k : M) (args : Fin 11 → M) (m : M) (hm : args 6 = m+1) :
    let r := F ones ![m,selectedTail args]
    let z := marker k args
    F PA194Stepper.stepper ![modelNumeral M 1,runTo4 k args] =
      F pairCode ![modelNumeral M 6,F pairCode ![z,(r+r+1)+(r+r+1)]] := by
  dsimp only
  have h := at4 k args
  dsimp only at h
  rw [hm] at h
  rw [h]
  exact PA194Site27BranchRows.positiveRow (marker k args) m (selectedTail args)
#print axioms at4
#print axioms zeroTo5
#print axioms positiveTo6
end models
end PA194Site3668Branch
