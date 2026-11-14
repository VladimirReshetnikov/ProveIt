import PA194FirstFourPositiveBlankTo7
import PA194PrefixReturn
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourPositiveReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourPositiveBlankTo7 PA194PrefixReturn PA194PrefixFile PA194CarryFile PA194ReturnFile PA194ReturnCell
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

theorem returnAfterBlank (n : Nat) (rest : Fin (n+1) → M) (l : M) :
    let x := F (PA194PrefixFile.leftCode n) (Fin.cases l rest)
    let six := ((1 : M)+1+1)+((1 : M)+1+1)
    let w := F ones ![(1 : M),six+six+1]
    let ret := F (PA194ReturnFile.returnCode n) (Fin.cases (w+w) rest)
    let c3 := ((1 : M)+1)+1
    let c6 := c3+c3
    let c13 := (c6+c6)+1
    F PA194Stepper.stepper ![c3+F (PA194CarryFile.costCode n) rest,
      F pairCode ![modelNumeral M 7,F pairCode ![(x+x)+(x+x)+1,c13]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+ret+ret]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := F (PA194PrefixFile.leftCode n) (Fin.cases l rest)
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let w := F ones ![(1 : M),six+six+1]
  have hone (v : M) : F ones ![(1 : M),v] = v+v+1 := by
    rw [← PA194StateOne.modelNumeralOne]
    change F ones ![F Code.succ (fun _ => modelNumeral M 0),v] = _
    rw [modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero,PA194StateOne.modelNumeralOne]
  have hfirst := modelReturnPrefixCell (1 : M) x six
  dsimp only at hfirst
  rw [hone,(modelOdd ((x+x)+(x+x)+1)).1,(modelOdd ((x+x)+(x+x)+1)).2] at hfirst
  have hc : (1 : M)+six+six = (((((1 : M)+1)+1)+(((1 : M)+1)+1))+((((1 : M)+1)+1)+(((1 : M)+1)+1)))+1 := by
    simp only [six,add_assoc,add_comm,add_left_comm]
  rw [hc] at hfirst
  have hreturn := modelReturnPrefixFile n rest l (w+w)
  dsimp only at hreturn
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hfirst]
  exact hreturn
theorem markerFirstFourPositiveBlankReturn (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
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
    let six := ((1 : M)+1+1)+((1 : M)+1+1)
    let w := F ones ![(1 : M),six+six+1]
    let ret := F (PA194ReturnFile.returnCode (n+1)) (Fin.cases (w+w) rest)
    ∃ time : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => scanned),
      F parityCode (fun _ => scanned)+ret+ret]] := by
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
  obtain ⟨time,hpath⟩ := markerFirstFourPositiveBlankTo7 n e rest u k ht hfirst hblank
  have hret := returnAfterBlank (n+1) rest scanned
  dsimp only at hret
  refine ⟨time+(((1 : M)+1)+1+F (PA194CarryFile.costCode (n+1)) rest),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hpath]
  exact hret
#print axioms markerFirstFourPositiveBlankReturn
#print axioms returnAfterBlank
end models
end PA194FirstFourPositiveReturn
