import PA194Site34ThirdTo1
import PA194Site34CarryTo4
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34To4
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

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  let c := (u+u)+(u+u)
  let vec : Fin 2 → M := ![e 0,c]
  let carry := ((k+1)+F (PA194CarryFile.costCode 1) vec)+modelNumeral M 2
  F addCode ![F addCode ![PA194Site34ThirdTo1.secondClock k args,modelNumeral M 13],carry]

theorem to4 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let tail := F (fileCode 8) (fun i => e i.succ.succ)
    let u := F ones ![e 1,tail]
    let c := (u+u)+(u+u)
    let vec : Fin 2 → M := ![e 0,c]
    let before := F ones ![k+1,modelNumeral M 800]
    let left := F (PA194CarryFile.leftCode 1) (Fin.cases before vec)
    let z := left+left+1
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,u]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  have h1 := PA194Site34ThirdTo1.to1 k args
  dsimp only at h1
  have h4 := PA194Site34CarryTo4.carryTo4 k (modelNumeral M 800) (e 0) u
  dsimp only at h4
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h1,h4]
#print axioms to4
end models
end PA194Site34To4
