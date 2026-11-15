import PA194Site39To16
import PA194SixteenScanExit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site39To17
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

theorem to17 (k : M) (args : Fin 11 → M) :
    let t := k
    let n := ((t+1)+1)
    let f := F sourceFileCode args
    let d := (1 : M)+(f+f)
    let v := (1 : M)+(d+d)
    let w := F ones ![t+1,v]
    let c := F addCode ![F addCode ![F addCode ![F addCode ![modelNumeral M 12,modelNumeral M 3],modelNumeral M 1],n+1],(1 : M)]
    F PA194Stepper.stepper ![F addCode ![c,(t+1)+1],
      PA194SourceSite31Physical.physicalFrame 39 n args] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 1613,(1 : M)+(w+w)+(w+w)]] := by
  dsimp only
  let t := k
  let n := ((t+1)+1)
  let b := F ones ![t+1,modelNumeral M 6454]
  let f := F sourceFileCode args
  let d := (1 : M)+(f+f)
  let v := (1 : M)+(d+d)
  let w := F ones ![t+1,v]
  have hb : b = F ones ![t,modelNumeral M 6454]+F ones ![t,modelNumeral M 6454]+1 := by
    dsimp only [b]
    change F ones ![F addCode ![t,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hr : (1 : M)+(1+1)+(d+d)+(d+d) = v+v+1 := by
    dsimp [v]; simp only [add_assoc,add_comm,add_left_comm]
  have h16 := PA194Site39To16.to16 k args
  dsimp only at h16
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![modelNumeral M 12,modelNumeral M 3],modelNumeral M 1],n+1],(1 : M)],
      PA194SourceSite31Physical.physicalFrame 39 n args] =
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => b),
        F parityCode (fun _ => b)+(1+1)+(d+d)+(d+d)]] at h16
  rw [hb,(modelOdd _).1,(modelOdd _).2,hr] at h16
  have hscan := PA194SixteenScanExit.modelScanExit t (modelNumeral M 3227) v
  have h200 : modelNumeral M 3227+modelNumeral M 3227 = modelNumeral M 6454 := by rw [←modelNumeralAdd]
  have h100 : modelNumeral M 3227 = modelNumeral M 1613+modelNumeral M 1613+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h200,h100,(modelOdd (modelNumeral M 1613)).1,(modelOdd (modelNumeral M 1613)).2] at hscan
  rw [PA194StepperCompose.modelStepperCompose,h16,hscan]
#print axioms to17
end models
end PA194Site39To17
