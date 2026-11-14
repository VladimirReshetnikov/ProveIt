import PA194FirstFourFirstTo61
import PA194State61To2
import PA194TwoScanInvariant
import PA194PrefixFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourPositiveFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourFirstTo61 PA194State61To2 PA194TwoScanInvariant PA194PrefixFile
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RegisterFile PA194MarkerScan PA194BinaryDouble PA194MarkAll PA194CarryFile
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

theorem markerFirstFourPositiveFile (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 4) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let l := ((a3+a3)+(a3+a3))+((a3+a3)+(a3+a3))
    let scanned := F ones ![k,l]
    let endLeft := F (PA194PrefixFile.leftCode (n+1)) (Fin.cases scanned rest)
    ∃ time : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![endLeft,rest (Fin.last (n+1))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let tail := F (fileCode (n+1)) rest
  let q := F ones ![k,tail]
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  let l := ((a3+a3)+(a3+a3))+((a3+a3)+(a3+a3))
  let markClock := (F (costCode 1) e+modelNumeral M 3)+F (costCode 1) e
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let start := F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![(((u+u)+(u+u))+((u+u)+(u+u))),F (fileCode 1) e]]
  have hq : F ones ![k+1,tail] = q+q+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hm := PA194FirstFourFirstTo61.markerFirstFourTo61 n e rest u (k+1) ht hfirst
  dsimp only at hm
  rw [hq] at hm
  have h61 := PA194State61To2.state61To2 a2 q
  dsimp only at h61
  have hscan := PA194TwoScanInvariant.modelFullScan k l tail
  let scanned := F ones ![k,l]
  have hfile := PA194PrefixFile.modelPrefixFile (n+1) rest scanned
  let t0 := ((markClock+headerClock)+modelNumeral M 3)+(modelNumeral M 4+1)
  refine ⟨((t0+modelNumeral M 10)+k)+F (PA194CarryFile.costCode (n+1)) rest,?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,_],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,h61,hscan,hfile]
#print axioms markerFirstFourPositiveFile
end models
end PA194FirstFourPositiveFile
