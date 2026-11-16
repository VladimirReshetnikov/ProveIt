import PA194HalfFileWithTail
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HalfFileTwoWithTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileWithTail PA194RightRows
open PA194RegisterFile PA194UnaryRuns PA194BinaryDouble BinaryTapeCodes
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

theorem scanTwoWithTail (n : Nat) (e : Fin (n+4) → M) (l p : M)
    (hp : F (fileCode (n+3)) e = p+p) :
    let x := F ones ![e ⟨0,by omega⟩+1,l]
    let a := F ones ![e ⟨1,by omega⟩,x+x]
    ∃ time right : M, F (fileCode (n+1)) (fun i => e ⟨i.val+2,by omega⟩) = right+right ∧
      F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 93,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have loop93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 93,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 93 1 93 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![x+x,y]] := by
    have hh := rightZero 93 0 113 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 113 1 113 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 14,F pairCode ![x+x,y]] := by
    have hh := rightZero 113 0 14 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  let e1 : Fin (n+3) → M := fun i => e i.succ
  let e2 : Fin (n+2) → M := fun i => e1 i.succ
  obtain ⟨r1,hr1,h1⟩ := scanHalfBlockWithTail (n+1) 93 113 e l p hp loop93 exit93
  let x := F ones ![e 0+1,l]
  let l1 := x+x
  obtain ⟨r2,hr2,h2⟩ := scanHalfBlockWithTail n 113 14 e1 l1 r1 hr1 loop113 exit113
  let a := F ones ![e1 0,l1]
  have ha : F ones ![e1 0+1,l1] = a+a+1 := by
    change F ones ![F addCode ![e1 0,F oneCode Fin.elim0],l1] = _
    rw [modelAddOne,modelOnesSucc]
  rw [ha] at h2
  have he : e2 = (fun i : Fin (n+2) => e ⟨i.val+2,by omega⟩) := by
    funext i
    congr 1
  change F (fileCode (n+1)) e2 = r2+r2 at hr2
  rw [he] at hr2
  refine ⟨((e 0+1)+1)+((e1 0+1)+1),r2,hr2,?_⟩
  change F PA194Stepper.stepper ![F addCode ![(e 0+1)+1,(e1 0+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  dsimp only [a,l1,x,e1]
  congr 1

/-- Two state-93/113 scans with exact time and right half, for any residual
file suffix. -/
theorem scanTwoWithTailExact (n : Nat) (e : Fin (n+4) → M) (l p : M)
    (hp : F (fileCode (n+3)) e = p+p) :
    let e1 : Fin (n+3) → M := fun i => e i.succ
    let e2 : Fin (n+2) → M := fun i => e1 i.succ
    let x := F ones ![e 0+1,l]
    let a := F ones ![e1 0,x+x]
    let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
    let clock := ((e 0+1)+1)+((e1 0+1)+1)
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 93,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),b+b+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have loop93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 93,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 93 1 93 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![x+x,y]] := by
    have hh := rightZero 93 0 113 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 113 1 113 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 14,F pairCode ![x+x,y]] := by
    have hh := rightZero 113 0 14 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  let e1 : Fin (n+3) → M := fun i => e i.succ
  let e2 : Fin (n+2) → M := fun i => e1 i.succ
  let r1 := F ones ![e1 0+1,F (fileCode (n+1)) (fun i => e1 i.succ)]
  let r2 := F ones ![e2 0+1,F (fileCode n) (fun i => e2 i.succ)]
  have hh1 := scanHalfBlockWithTailExact (n+1) 93 113 e l p hp loop93 exit93
  dsimp only at hh1
  obtain ⟨hr1,h1⟩ := hh1
  change F (fileCode (n+2)) e1 = r1+r1 at hr1
  let x := F ones ![e 0+1,l]
  have hh2 := scanHalfBlockWithTailExact n 113 14 e1 (x+x) r1 hr1 loop113 exit113
  dsimp only at hh2
  obtain ⟨hr2,h2⟩ := hh2
  let a := F ones ![e1 0,x+x]
  let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
  have ha : F ones ![e1 0+1,x+x] = a+a+1 := by
    change F ones ![F addCode ![e1 0,F oneCode Fin.elim0],x+x] = _
    rw [modelAddOne,modelOnesSucc]
  have hb : r2 = b+b+1 := by
    change F ones ![F addCode ![e2 0,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [ha] at h2
  change F PA194Stepper.stepper ![(e1 0+1)+1,
    F pairCode ![modelNumeral M 113,F pairCode ![x+x,r1]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),r2]] at h2
  rw [hb] at h2
  change F PA194Stepper.stepper ![F addCode ![(e 0+1)+1,(e1 0+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1]
  exact h2
#print axioms scanTwoWithTailExact
#print axioms scanTwoWithTail
end models
end PA194HalfFileTwoWithTail
