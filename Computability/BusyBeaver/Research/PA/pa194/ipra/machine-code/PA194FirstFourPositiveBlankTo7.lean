import PA194FirstFourPositiveFile
import PA194SelectedEntry
import PA194CarryEntry
import PA194ThreeBlankTail
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourPositiveBlankTo7
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourPositiveFile PA194SelectedEntry PA194CarryEntry PA194ThreeBlankTail
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RegisterFile PA194MarkerScan PA194BinaryDouble
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

theorem endTo7 (l : M) :
    let a := (l+l)+(l+l)+1
    let c3 := ((1 : M)+1)+1
    let c6 := c3+c3
    let c13 := (c6+c6)+1
    F PA194Stepper.stepper ![(((1 : M)+1)+1)+modelNumeral M 5,
      F pairCode ![modelNumeral M 2,F pairCode ![l,(0 : M)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,c13]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let start := F pairCode ![modelNumeral M 2,F pairCode ![l,(0 : M)]]
  let a := (l+l)+(l+l)+1
  have hs (time conf : M) : F PA194Stepper.stepper ![time+1,conf] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![time,conf]) := by
    change F PA194Stepper.stepper ![F addCode ![time,F oneCode Fin.elim0],conf] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have h3 : F PA194Stepper.stepper ![((1 : M)+1)+1,start] =
      F pairCode ![modelNumeral M 3,F pairCode ![a+a+1,(0 : M)]] := by
    rw [hs,hs]
    have h1 : F PA194Stepper.stepper ![(1 : M),start] =
        F PackedClock.encodedStep (fun _ => start) := by
      have h := hs (0 : M) start
      have hz := PA194Stepper.modelStepperZero start
      change F PA194Stepper.stepper ![(0 : M),start] = start at hz
      rw [hz] at h
      simpa using h
    rw [h1]
    have he1 : F PackedClock.encodedStep (fun _ => start) =
        F pairCode ![modelNumeral M 0,F pairCode ![l+l,(0 : M)]] := by
      simpa [start] using modelPackedTwoEven l (0 : M)
    have he2 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 0,F pairCode ![l+l,(0 : M)]]) =
        F pairCode ![modelNumeral M 1,F pairCode ![a,(0 : M)]] := by
      simpa [a] using modelPackedZeroEven (l+l) (0 : M)
    have he3 : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 1,F pairCode ![a,(0 : M)]]) =
        F pairCode ![modelNumeral M 3,F pairCode ![a+a+1,(0 : M)]] := by
      simpa using modelPackedCarryOne a (0 : M)
    rw [he1,he2,he3]
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h3]
  exact PA194ThreeBlankTail.modelThreeBlankTail a
theorem markerFirstFourPositiveBlankTo7 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 4)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
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
    let a := (endLeft+endLeft)+(endLeft+endLeft)+1
    let c3 := ((1 : M)+1)+1
    let c6 := c3+c3
    let c13 := (c6+c6)+1
    ∃ time : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,c13]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
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
  obtain ⟨time,hfile⟩ := markerFirstFourPositiveFile n e rest u k ht hfirst
  rw [hblank] at hfile
  refine ⟨time+(((1 : M)+1)+1)+modelNumeral M 5,?_⟩
  rw [add_assoc]
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hfile]
  exact endTo7 endLeft
#print axioms markerFirstFourPositiveBlankTo7
#print axioms endTo7
end models
end PA194FirstFourPositiveBlankTo7
