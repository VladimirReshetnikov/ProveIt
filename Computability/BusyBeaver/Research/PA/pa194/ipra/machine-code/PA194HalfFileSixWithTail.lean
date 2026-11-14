import PA194HalfFileWithTail
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HalfFileSixWithTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileWithTail PA194RightRows PA194RegisterFile PA194UnaryRuns PA194StateOne
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

theorem scanSixExact (n : Nat) (e : Fin (n+8) → M) (l p : M)
    (hp : F (fileCode (n+7)) e = p+p) :
    let e0 := e
    let e1 : Fin (n+7) → M := fun j => e0 j.succ
    let e2 : Fin (n+6) → M := fun j => e1 j.succ
    let e3 : Fin (n+5) → M := fun j => e2 j.succ
    let e4 : Fin (n+4) → M := fun j => e3 j.succ
    let e5 : Fin (n+3) → M := fun j => e4 j.succ
    let e6 : Fin (n+2) → M := fun j => e5 j.succ
    let x1 := F ones ![e0 0+1,l]
    let l1 := x1+x1
    let t1 := (e0 0+1)+1
    let x2 := F ones ![e1 0+1,l1]
    let l2 := x2+x2
    let t2 := (e1 0+1)+1
    let x3 := F ones ![e2 0+1,l2]
    let l3 := x3+x3
    let t3 := (e2 0+1)+1
    let x4 := F ones ![e3 0+1,l3]
    let l4 := x4+x4
    let t4 := (e3 0+1)+1
    let x5 := F ones ![e4 0+1,l4]
    let l5 := x5+x5
    let t5 := (e4 0+1)+1
    let x6 := F ones ![e5 0+1,l5]
    let l6 := x6+x6
    let t6 := (e5 0+1)+1
    let r6 := F ones ![e6 0+1,F (fileCode n) (fun i => e6 i.succ)]
    F (fileCode (n+1)) e6 = r6+r6 ∧
    F PA194Stepper.stepper ![(((((t1+t2)+t3)+t4)+t5)+t6),
      F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![l6,r6]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have loop71 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 71,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 71 1 71 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit71 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 95,F pairCode ![x+x,y]] := by
    have hh := rightZero 71 0 95 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop95 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 95,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 95,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 95 1 95 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit95 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 95,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 114,F pairCode ![x+x,y]] := by
    have hh := rightZero 95 0 114 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop114 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 114,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 114 1 114 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit114 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 68,F pairCode ![x+x,y]] := by
    have hh := rightZero 114 0 68 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
  have loop68 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 68,F pairCode ![x+x+1,y]] := by
    have hh := rightOne 68 1 68 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using hh
  have exit68 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M 93,F pairCode ![x+x,y]] := by
    have hh := rightZero 68 0 93 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using hh
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
  let e0 := e
  let e1 : Fin (n+7) → M := fun j => e0 j.succ
  let e2 : Fin (n+6) → M := fun j => e1 j.succ
  let e3 : Fin (n+5) → M := fun j => e2 j.succ
  let e4 : Fin (n+4) → M := fun j => e3 j.succ
  let e5 : Fin (n+3) → M := fun j => e4 j.succ
  let e6 : Fin (n+2) → M := fun j => e5 j.succ
  let r1 := F ones ![e1 0+1,F (fileCode (n+5)) (fun j => e1 j.succ)]
  let x1 := F ones ![e0 0+1,l]
  let l1 := x1+x1
  let t1 := (e0 0+1)+1
  have hh1 := scanHalfBlockWithTailExact (n+5) 71 95 e0 l p hp loop71 exit71
  dsimp only at hh1
  have hr1 := hh1.1
  have h1 := hh1.2
  let r2 := F ones ![e2 0+1,F (fileCode (n+4)) (fun j => e2 j.succ)]
  let x2 := F ones ![e1 0+1,l1]
  let l2 := x2+x2
  let t2 := (e1 0+1)+1
  have hh2 := scanHalfBlockWithTailExact (n+4) 95 114 e1 l1 r1 hr1 loop95 exit95
  dsimp only at hh2
  have hr2 := hh2.1
  have h2 := hh2.2
  let r3 := F ones ![e3 0+1,F (fileCode (n+3)) (fun j => e3 j.succ)]
  let x3 := F ones ![e2 0+1,l2]
  let l3 := x3+x3
  let t3 := (e2 0+1)+1
  have hh3 := scanHalfBlockWithTailExact (n+3) 114 68 e2 l2 r2 hr2 loop114 exit114
  dsimp only at hh3
  have hr3 := hh3.1
  have h3 := hh3.2
  let r4 := F ones ![e4 0+1,F (fileCode (n+2)) (fun j => e4 j.succ)]
  let x4 := F ones ![e3 0+1,l3]
  let l4 := x4+x4
  let t4 := (e3 0+1)+1
  have hh4 := scanHalfBlockWithTailExact (n+2) 68 93 e3 l3 r3 hr3 loop68 exit68
  dsimp only at hh4
  have hr4 := hh4.1
  have h4 := hh4.2
  let r5 := F ones ![e5 0+1,F (fileCode (n+1)) (fun j => e5 j.succ)]
  let x5 := F ones ![e4 0+1,l4]
  let l5 := x5+x5
  let t5 := (e4 0+1)+1
  have hh5 := scanHalfBlockWithTailExact (n+1) 93 113 e4 l4 r4 hr4 loop93 exit93
  dsimp only at hh5
  have hr5 := hh5.1
  have h5 := hh5.2
  let r6 := F ones ![e6 0+1,F (fileCode (n+0)) (fun j => e6 j.succ)]
  let x6 := F ones ![e5 0+1,l5]
  let l6 := x6+x6
  let t6 := (e5 0+1)+1
  have hh6 := scanHalfBlockWithTailExact (n+0) 113 14 e5 l5 r5 hr5 loop113 exit113
  dsimp only at hh6
  have hr6 := hh6.1
  have h6 := hh6.2
  have chain2 : F PA194Stepper.stepper ![(t1+t2),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 114,F pairCode ![l2,r2]] := by
    change F PA194Stepper.stepper ![F addCode ![t1,t2],_] = _
    rw [PA194StepperCompose.modelStepperCompose,h1,h2]
  have chain3 : F PA194Stepper.stepper ![((t1+t2)+t3),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 68,F pairCode ![l3,r3]] := by
    change F PA194Stepper.stepper ![F addCode ![(t1+t2),t3],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain2,h3]
  have chain4 : F PA194Stepper.stepper ![(((t1+t2)+t3)+t4),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 93,F pairCode ![l4,r4]] := by
    change F PA194Stepper.stepper ![F addCode ![((t1+t2)+t3),t4],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain3,h4]
  have chain5 : F PA194Stepper.stepper ![((((t1+t2)+t3)+t4)+t5),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 113,F pairCode ![l5,r5]] := by
    change F PA194Stepper.stepper ![F addCode ![(((t1+t2)+t3)+t4),t5],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain4,h5]
  have chain6 : F PA194Stepper.stepper ![(((((t1+t2)+t3)+t4)+t5)+t6),F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![l6,r6]] := by
    change F PA194Stepper.stepper ![F addCode ![((((t1+t2)+t3)+t4)+t5),t6],_] = _
    rw [PA194StepperCompose.modelStepperCompose,chain5,h6]
  exact ⟨hr6,chain6⟩
#print axioms scanSixExact
end models
end PA194HalfFileSixWithTail
