import PA194Site34To4
import PA194Site27BranchRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34Branch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def selectedTail (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  F (fileCode 8) (fun i => e i.succ.succ)
noncomputable def marker (k : M) (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  let u := F ones ![e 1,selectedTail args]
  let c := (u+u)+(u+u)
  let vec : Fin 2 → M := ![e 0,c]
  let before := F ones ![k+1,modelNumeral M 800]
  let left := F (PA194CarryFile.leftCode 1) (Fin.cases before vec)
  left+left+1
noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  F addCode ![PA194Site34To4.clock k args,modelNumeral M 1]

theorem zeroTo5 (k : M) (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    let e := physicalArgs args
    let t := F ones ![e 2+1,F (fileCode 7) (fun i => e i.succ.succ.succ)]
    let z := marker k args
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]] := by
  dsimp only
  let e := physicalArgs args
  let t := F ones ![e 2+1,F (fileCode 7) (fun i => e i.succ.succ.succ)]
  have ht : selectedTail args = t+t := by
    dsimp only [selectedTail,t]
    rw [modelFileSucc,modelBlock]
    rfl
  have hv : e 1 = (0 : M) := hz
  have h := PA194Site34To4.to4 k args
  dsimp only at h
  change F PA194Stepper.stepper ![PA194Site34To4.clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
    F pairCode ![modelNumeral M 4,F pairCode ![(marker k args)+(marker k args),F ones ![e 1,selectedTail args]]] at h
  rw [hv,ht] at h
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h]
  exact PA194Site27BranchRows.zeroRow (marker k args) t

theorem positiveTo6 (k : M) (args : Fin 11 → M) (m : M) (hm : args 8 = m+1) :
    let r := F ones ![m,selectedTail args]
    let z := marker k args
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 6,F pairCode ![z,(r+r+1)+(r+r+1)]] := by
  dsimp only
  have hv : physicalArgs args 1 = m+1 := hm
  have h := PA194Site34To4.to4 k args
  dsimp only at h
  change F PA194Stepper.stepper ![PA194Site34To4.clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
    F pairCode ![modelNumeral M 4,F pairCode ![(marker k args)+(marker k args),F ones ![physicalArgs args 1,selectedTail args]]] at h
  rw [hv] at h
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h]
  exact PA194Site27BranchRows.positiveRow (marker k args) m (selectedTail args)
#print axioms zeroTo5
#print axioms positiveTo6
end models
end PA194Site34Branch
