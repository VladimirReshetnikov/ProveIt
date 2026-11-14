import PA194EightyFourScan
import PA194GenericZeroToOneScan
import PA194EightyFourExit
import PA194RightRows
import PA194HeaderController
import PA194BinaryDouble
import PA194FifteenExitComposition
import PA194SixteenScanExit
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194EightyFourTo17
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RightRows PA194EightyFourExit PA194EightyFourScan
open PackedIterationModel ConfigurationStep PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnedFileTo17 (k a r : M) :
    let t := (1 : M)+(r+r)+(r+r)
    let s := (1 : M)+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))
    let w := F ones ![k+1,s]
    F PA194Stepper.stepper ![(((((k+1)+1)+1)+1)+((k+1)+1)),F pairCode ![modelNumeral M 84,
      F pairCode ![a+a,F zeros ![modelNumeral M 2,F zeros ![k,t]]]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => a),
      F parityCode (fun _ => a)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let t := (1 : M)+(r+r)+(r+r)
  let b := F ones ![k,a+a]
  let s := (1 : M)+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))
  have h1 := returnedFileScan k (a+a) r
  dsimp only at h1
  have hb : F ones ![k+1,a+a] = b+b+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hb] at h1
  have hs : s = (t+t)+1 := by dsimp [s,t]; simp only [add_assoc,add_comm,add_left_comm]
  change _ = F pairCode ![modelNumeral M 15,F pairCode ![b+b+1,s]] at h1
  rw [hs] at h1
  have h2 := PA194FifteenExitComposition.modelPackedExit15 (b+b+1) t
  rw [(PA194BinaryDouble.modelOdd b).1,(PA194BinaryDouble.modelOdd b).2] at h2
  have hright : (1 : M)+(1+1)+(t+t)+(t+t) = (s+s)+1 := by
    dsimp [s,t]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at h2
  have h3 := PA194SixteenScanExit.modelScanExit k a s
  let initial := F pairCode ![modelNumeral M 84,F pairCode ![a+a,F zeros ![modelNumeral M 2,F zeros ![k,t]]]]
  have h12 : F PA194Stepper.stepper ![(((k+1)+1)+1)+1,initial] =
      F pairCode ![modelNumeral M 16,F pairCode ![b,s+s+1]] := by
    change F PA194Stepper.stepper ![F addCode ![((k+1)+1)+1,F oneCode Fin.elim0],initial] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc,h1,h2]
  change F PA194Stepper.stepper ![F addCode ![(((k+1)+1)+1)+1,(k+1)+1],initial] = _
  rw [PA194StepperCompose.modelStepperCompose,h12,h3]
#print axioms returnedFileTo17
end models
end PA194EightyFourTo17
