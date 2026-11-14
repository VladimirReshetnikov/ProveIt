import PA194ZerosDouble
import PA194SelectedZeroFifteenReturn
import PA194ZeroScanInvariant
import PA194FifteenExitComposition
import PA194MarkerReturnCell
import PA194RollbackCell
import PA194ReturnCell
import PA194ReturnFileMeaning
import PA194StepperCompose
import PA194ReturnedDecrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SelectedZeroActualReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZerosDouble PA194SelectedZeroFifteenReturn PA194BinaryDouble PA194ZeroScanInvariant PA194FifteenExitComposition PA194MarkerReturnCell PA194StateOne PA194ZeroRuns
open PRAExhaustion PA194RollbackCell PA194BinaryDouble
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ReturnCell PA194ReturnFileMeaning PA194BinaryDouble
open PA194ReturnedDecrement PA194MarkedFile PA194CarryFile PA194ReturnFile
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The state-15 shape from the selected-zero scanner returns to state 17. -/
theorem actualTo17 (m s r : M) :
    let g := s+s
    let h := g+g+1
    let xx := h+h+1
    let l := xx+xx+1
    let q := F zeros ![m,F zeros ![modelNumeral M 6,l]+F zeros ![modelNumeral M 6,l]]
    let t := (1 : M)+(r+r)+(r+r)
    let b := F zeros ![modelNumeral M 5,F zeros ![m,t]]
    let w := F ones ![modelNumeral M 2,1+(b+b)+(b+b)]
    F PA194Stepper.stepper ![((m+modelNumeral M 5)+1)+((modelNumeral M 2+1)+1),
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => F halfCode (fun _ => q)),
        F parityCode (fun _ => F halfCode (fun _ => q))+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => s),
      F parityCode (fun _ => s)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := s+s
  let h := g+g+1
  let xx := h+h+1
  let l := xx+xx+1
  let z := F zeros ![modelNumeral M 5,l]
  let d := F zeros ![m,z]
  have h6 : F zeros ![modelNumeral M 6,l] = z+z := by
    rw [show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,modelZerosSucc]
  have hq : F zeros ![m,F zeros ![modelNumeral M 6,l]+F zeros ![modelNumeral M 6,l]] = (d+d)+(d+d) := by
    rw [h6,modelZerosDouble,modelZerosDouble]
  rw [hq,(modelDouble (d+d)).2,(modelDouble d).2,(modelDouble d).1,zero_add]
  have ht (x : M) : (1 : M)+(1 : M)+(x+x)+(x+x) = (1+x+x)+(1+x+x) := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [ht]
  exact fifteenTo17 m s r
#print axioms actualTo17
end models
end PA194SelectedZeroActualReturn
