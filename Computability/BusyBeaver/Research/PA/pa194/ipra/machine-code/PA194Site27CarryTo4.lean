import PA194ScanInvariant
import PA194CarryFile
import PA194ThirdPassTo4
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27CarryTo4
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194UnaryRuns PA194OnesCommute PA194RegisterFile
open PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem carryTo4 (k l : M) (e : Fin 11 → M) :
    let e6 : Fin 5 → M := fun i => e ⟨i.val+6,by omega⟩
    let tail := F (fileCode 3) (fun i => e6 i.succ)
    let q := F ones ![e6 0,tail]
    let vec : Fin 7 → M := ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
    let file := F (fileCode 6) vec
    let before := F ones ![k+1,l]
    let left := F (PA194CarryFile.leftCode 6) (Fin.cases before vec)
    let z := left+left+1
    let time := ((k+1)+F (PA194CarryFile.costCode 6) vec)+modelNumeral M 2
    F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 1,F pairCode ![l,F ones ![k,file+file+1]]]] =
    F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let e6 : Fin 5 → M := fun i => e ⟨i.val+6,by omega⟩
  let tail := F (fileCode 3) (fun i => e6 i.succ)
  let q := F ones ![e6 0,tail]
  let vec : Fin 7 → M := ![e 0,e 1,e 2,e 3,e 4,e 5,(q+q)+(q+q)]
  let file := F (fileCode 6) vec
  let before := F ones ![k+1,l]
  let left := F (PA194CarryFile.leftCode 6) (Fin.cases before vec)
  let cost := F (PA194CarryFile.costCode 6) vec
  have hon : F ones ![k,file+file+1] = F ones ![k+1,file] := by
    rw [modelOnesCommute]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],file]
    rw [modelAddOne,modelOnesSucc]
  rw [hon]
  have hs := PA194ScanInvariant.modelFullScan (k+1) l file
  have hc := PA194CarryFile.modelCarryFile 6 vec before
  change F PA194Stepper.stepper ![cost,F pairCode ![(1 : M),F pairCode ![before,file]]] =
    F pairCode ![(1 : M),F pairCode ![left,(q+q)+(q+q)]] at hc
  have h2 := PA194ThirdPassTo4.twoTo4 left q
  rw [modelNumeralOne] at h2 ⊢
  change F PA194Stepper.stepper ![F addCode ![(k+1)+cost,modelNumeral M 2],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 2,F PA194Stepper.stepper ![F addCode ![k+1,cost],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hs,hc,h2]
#print axioms carryTo4
end models
end PA194Site27CarryTo4
