import PA194Site28ReturnHeader
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194UnaryRuns BinaryTapeCodes TableDispatch PA194Site28ReturnHeader PA194SeedHeaderTo21 PA194LeftOneWriteOne PA194BinaryDouble PA194FirstThreeBlankTailTo16 PA194Site27PositiveReturnFrom16 PA194ZeroRuns PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem oneFrom16Odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 16 16 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem headerTo24 (k p : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let j := a6+a6+1
    let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
    let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    let r1 := (1 : M)+r+r
    let r2 := r1+r1+1
    let x := (1+1)+(r2+r2)+(r2+r2)
    let t := (1 : M)+x+x
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+rc),
      F PA194Stepper.stepper ![(1 : M),
        F PA194Stepper.stepper ![(1 : M),
          F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
            F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
              F PA194Stepper.stepper ![modelNumeral M 2,
                F pairCode ![modelNumeral M 7,F pairCode ![j+j,(w+w)+(w+w)]]]]]]]] =
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
  let j := a6+a6+1
  let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
  let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  let r1 := (1 : M)+r+r
  let r2 := r1+r1+1
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h12 := twoTo12 (M := M) j w
  have h14 := scansTo14 (M := M) j k p
  dsimp only at h14
  have h16 := header14To16 (M := M) k j p
  dsimp only at h16
  rw [(modelOdd a6).1,(modelOdd a6).2] at h16
  have hright : (1 : M)+(1+1)+(r+r)+(r+r) = r1+r1+1 := by
    dsimp only [r1]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at h16
  have hone (z : M) : F PA194Stepper.stepper ![(1 : M),z] = F PackedClock.encodedStep (fun _ => z) := by
    rw [←modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),z] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  have hrow1 := oneFrom16Odd (M := M) a5 r1
  have hrow2 := oneFrom16 (M := M) a4 r2
  have hright1 : (r1+r1+1)+(r1+r1+1)+1 = r2+r2+1 := by rfl
  rw [hright1] at hrow1
  have hright2 : (r2+r2+1)+(r2+r2+1) = (1+1)+(r2+r2)+(r2+r2) := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hright2] at hrow2
  have hr := returnFrom16 (M := M) r2
  dsimp only at hr
  have hrow1' : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,F pairCode ![a6,r1+r1+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a5,r2+r2+1]] := by
    rw [hone,hrow1]
  have hrow2' : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,F pairCode ![a5,r2+r2+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a4,(1+1)+(r2+r2)+(r2+r2)]] := by
    rw [hone,hrow2]
  rw [h12,h14,h16,hrow1',hrow2',hr]
#print axioms oneFrom16Odd
#print axioms headerTo24
end models
end PA194Site29ReturnHeader
