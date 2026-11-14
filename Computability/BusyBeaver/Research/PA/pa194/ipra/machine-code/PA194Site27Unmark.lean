import PA194SixteenScanInvariant
import PA194SixteenExitComposition
import PA194ZeroReturnFrom16
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27Unmark
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194LeftOneWriteOne PA194ZeroReturnFrom16
open PA194SixteenExitComposition PA194BinaryDouble PA194UnaryRuns BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem return17To24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let w4 := w3+w3
    let w5 := w4+w4
    let w6 := w5+w5
    let w7 := w6+w6
    let w8 := w7+w7
    let o2 := (1 : M)+1
    let o4 := o2+o2
    let o8 := o4+o4
    let o16 := o8+o8
    let t := (1 : M)+w3+w3
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 3+(modelNumeral M 3+rc),F pairCode ![modelNumeral M 17,F pairCode ![a5,w2]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let w4 := w3+w3
  let w5 := w4+w4
  let w6 := w5+w5
  let w7 := w6+w6
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  have h18 := row18Odd a3 w2
  have h19 := leftOneWriteOne 19 16 (by decide) (by decide +kernel) a3 w3
  rw [(modelDouble a2).1,(modelDouble a2).2,zero_add] at h19
  have h19' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![a3,w4+1]]) =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(w3+w3)+(w3+w3)]] := by
    convert h19 using 1 <;> dsimp only [w4,w3] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h3 : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 17,F pairCode ![a4+a4,w2]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(w3+w3)+(w3+w3)]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17,h18,h19']
  have hr := PA194ZeroReturnFrom16.returnFrom16 w3
  dsimp only at hr
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,modelNumeral M 3+rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h3,hr]
theorem unmarkTo24 (k out : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5
    let base := a6+a6
    let b := F ones ![k+1,base]
    let q := out+out+1
    let w := F ones ![k+1,q]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let t := (1 : M)+w3+w3
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((((1 : M)+k)+1)+1)+(modelNumeral M 3+(modelNumeral M 3+rc))),
      F pairCode ![modelNumeral M 17,F pairCode ![b,(1 : M)+out+out]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5
  let base := a6+a6
  let x := F ones ![k,base]
  let q := out+out+1
  let w := F ones ![k+1,q]
  let w0 := F ones ![k,q]
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have hb : F ones ![k+1,base] = x+x+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],base] = _
    rw [modelAddOne,modelOnesSucc]
  have hw : w=w0+w0+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],q] = _
    rw [modelAddOne,modelOnesSucc]
  have h17 := leftOneWriteOne 17 16 (by decide) (by decide +kernel) (x+x+1) out
  rw [(modelOdd x).1,(modelOdd x).2] at h17
  have h17' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![x+x+1,(1 : M)+out+out]]) =
      F pairCode ![modelNumeral M 16,F pairCode ![x,q+q+1]] := by
    convert h17 using 1 <;> (try dsimp [q]) <;> simp only [add_assoc,add_comm,add_left_comm]
  have hs := PA194SixteenScanInvariant.modelFullScan k base q
  have hb16 := modelPackedBoundary16 a6 w0
  rw [←hw] at hb16
  have he16 := modelPackedExit16 a6 w
  rw [(modelDouble a5).1,(modelDouble a5).2,zero_add] at he16
  have hr := return17To24 w
  dsimp only at hr
  rw [hb]
  change F PA194Stepper.stepper ![F addCode ![((((1 : M)+k)+1)+1),modelNumeral M 3+(modelNumeral M 3+rc)],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![(((1 : M)+k)+1),F oneCode Fin.elim0],_]] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PA194Stepper.stepper ![_,F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![(1 : M)+k,F oneCode Fin.elim0],_])] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PA194Stepper.stepper ![_,F PackedClock.encodedStep (fun _ => F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![(1 : M),k],_]))] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have hstep : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 17,F pairCode ![x+x+1,(1 : M)+out+out]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![x,q+q+1]] := by
    nth_rewrite 1 [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17']
  rw [hstep,hs,hb16,he16,hr]
#print axioms unmarkTo24
#print axioms return17To24
end models
end PA194Site27Unmark
