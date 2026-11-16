import PA194Site3671To15
import PA194FifteenExitComposition
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3671To16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to16 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let b := F ones ![k+1,modelNumeral M 14]
    let f := F sourceFileCode args
    let d := (1 : M)+(f+f)
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 1],n+1],(1 : M)],
      PA194SourceSite31Physical.physicalFrame 3671 n args] =
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => b),
        F parityCode (fun _ => b)+(1+1)+(d+d)+(d+d)]] := by
  dsimp only
  let m := k+1
  let n := m+1
  let b := F ones ![m,modelNumeral M 14]
  let f := F sourceFileCode args
  let d := (1 : M)+(f+f)
  have ha : F ones ![n,modelNumeral M 14] = b+b+1 := by
    dsimp only [n,b]
    change F ones ![F addCode ![m,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h15 := PA194Site3671To15.to15 k args
  dsimp only at h15
  rw [ha,(modelOdd b).1,(modelOdd b).2] at h15
  have hr : (1 : M)+(1+1)+(f+f)+(f+f) = d+d+1 := by
    dsimp [d]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hr] at h15
  have h16 := PA194FifteenExitComposition.modelPackedExit15 b d
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 1],n+1],(1 : M)],_] = _
  rw [show F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 1],n+1],(1 : M)] =
      F Code.succ (fun _ => F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 1],n+1]) from modelAddOne _,
    PA194Stepper.modelStepperSucc,h15,h16]
#print axioms to16
end models
end PA194Site3671To16
