import PA194Site27PositiveHeaderTo12
import PA194ThirteenExitComposition
import PA194FirstThreeBlankTailTo16
import PA194Site27PositiveReturnFrom16
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28ReturnHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194RightRows PA194LeftOneWriteOne PA194BinaryDouble PA194HeaderController PA194UnaryRuns PA194ZeroRuns PA194ZerosDouble PA194StateOne PA194OnesCommute PA194FirstThreeBlankTailTo16 PA194Site27PositiveReturnFrom16 PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem twoTo12 (j w : M) :
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 7,
      F pairCode ![j+j,(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,(w+w)+(w+w)]] := by
  have h7 := rowEvenLeft (M := M) 7 9 (by decide) (by decide +kernel)
  have h9 := rightZero (M := M) 9 1 12 (by decide) (by decide +kernel)
  simp only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] at h9
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,h7,h9]
theorem scansTo14 (j k p : M) :
    let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
    let x := (j+j+1)+(j+j+1)
    let y := F zeros ![k,x]
    F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
      F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![y+y,(p+p)+(p+p)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
  let x := (j+j+1)+(j+j+1)
  let y := F zeros ![k,x]
  have hw : w = F ones ![k,p+p]+F ones ![k,p+p]+1 := by
    dsimp only [w]
    have ha : (1 : M)+(p+p)+(p+p) = (p+p)+(p+p)+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [ha,modelOnesCommute]
  have h := PA194ThirteenExitComposition.modelTwoScansExit (M := M) (modelNumeral M 2) k (j+j+1) p
  simp only [zerosTwo] at h
  rw [←hw] at h
  let z := F zeros ![k,j+j+1]
  have hx : y=z+z := by dsimp only [y,x,z]; rw [modelZerosDouble]
  have hl : F zeros ![k,((j+j+1)+(j+j+1))+((j+j+1)+(j+j+1)) +
      (((j+j+1)+(j+j+1))+((j+j+1)+(j+j+1)))] = (y+y)+(y+y) := by
    rw [modelZerosDouble,modelZerosDouble]
  rw [hl,(modelDouble (y+y)).1,(modelDouble (y+y)).2,zero_add] at h
  exact h
theorem oneFrom16 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 16 16 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem headerTo24 (k p : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6
    let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
    let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    let r1 := (1 : M)+r+r
    let x := (1+1)+(r1+r1)+(r1+r1)
    let t := (1 : M)+x+x
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+rc),
      F PA194Stepper.stepper ![(1 : M),
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,
              F pairCode ![modelNumeral M 7,F pairCode ![a7,(w+w)+(w+w)]]]]]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5+1
  let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
  let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  let r1 := (1 : M)+r+r
  let c := ((1 : M)+k)+modelNumeral M 3
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h12 := twoTo12 (M := M) a6 w
  have h14 := scansTo14 (M := M) a6 k p
  dsimp only at h14
  have h16 := header14To16 (M := M) k a6 p
  dsimp only at h16
  rw [(modelOdd a5).1,(modelOdd a5).2] at h16
  have hrow := oneFrom16 (M := M) a4 r1
  have hr := returnFrom16 (M := M) r1
  dsimp only at hr
  have hright : (1 : M)+(1+1)+(r+r)+(r+r) = r1+r1+1 := by
    dsimp only [r1]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at h16
  have hone (z : M) : F PA194Stepper.stepper ![(1 : M),z] = F PackedClock.encodedStep (fun _ => z) := by
    rw [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),z] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  have hrow' : F PA194Stepper.stepper ![(1 : M),
      F pairCode ![modelNumeral M 16,F pairCode ![a4+a4,r1+r1+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a4,(r1+r1+1)+(r1+r1+1)]] := by
    rw [hone,hrow]
  have hright2 : (r1+r1+1)+(r1+r1+1) = (1+1)+(r1+r1)+(r1+r1) := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hright2] at hrow'
  rw [h12,h14,h16,hrow',hr]
#print axioms headerTo24
#print axioms oneFrom16
#print axioms scansTo14
#print axioms twoTo12
end models
end PA194Site28ReturnHeader
