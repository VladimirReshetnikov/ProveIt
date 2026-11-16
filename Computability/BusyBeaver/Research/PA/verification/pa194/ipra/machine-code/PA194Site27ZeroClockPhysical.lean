import PA194Site27ZeroExactClock
import PA194Site27ZeroTo12
import PA194Site27ZeroTo14
import PA194Site27ZeroTo24
import PA194Site27ZeroPath
import PA194CarryAppendZero
import PA194RollbackFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroClockPhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open BinaryTapeCodes PA194ReturnFile PRAModelIOpenPairing PA194BinaryDouble PA194SourceSite25Physical PA194Site27ZeroExact PA194Site27ZeroExactClock PA194Site27ZeroRollback PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def clock11 (k : M) (e : Fin 11 → M) : M :=
  F addCode ![F addCode ![clock4 k e,modelNumeral M 1],modelNumeral M 2]
noncomputable def clockRollback (k : M) (e : Fin 11 → M) : M :=
  F addCode ![clock11 k e,F (PA194CarryFile.costCode 7) (seven e)]
noncomputable def clock12 (k : M) (e : Fin 11 → M) : M :=
  F addCode ![F addCode ![clockRollback k e,k+1],modelNumeral M 4]
noncomputable def clock14 (k : M) (e : Fin 11 → M) : M :=
  F addCode ![clock12 k e,((modelNumeral M 2+1)+(k+1))+1]
noncomputable def clock24 (k : M) (e : Fin 11 → M) : M :=
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c16 := ((1 : M)+(k+1))+modelNumeral M 3
  F addCode ![F addCode ![F addCode ![clock14 k e,c16],(1 : M)],modelNumeral M 3+rc]

theorem zeroRollback (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    F PA194Stepper.stepper ![clockRollback k e,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
        F parityCode (fun _ => before k)+returned e+returned e]] := by
  let t := tailWord e
  let z := selectedCarry k e + selectedCarry k e + 1
  have hstart := PA194Site27ZeroExactClock.zeroTo11Exact k e hz
  dsimp only at hstart
  have hroll := PA194RollbackFile.modelRollbackPrefix 7 (seven e) (before k) (t+t)
  dsimp only at hroll
  have hc := carriedIsSeven k e
  dsimp only at hc
  rw [hc,(modelDouble z).1,(modelDouble z).2] at hroll
  simp only [zero_add] at hroll
  change F PA194Stepper.stepper ![F (PA194CarryFile.costCode 7) (seven e),
    F pairCode ![modelNumeral M 11,F pairCode ![z,(t+t)+(t+t)]]] = _ at hroll
  change F PA194Stepper.stepper ![F addCode ![clock11 k e,F (PA194CarryFile.costCode 7) (seven e)],_] = _
  dsimp only [clock11]
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact hroll
theorem zeroTo12 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let w := F ones ![k+1,returned e]
    let p := w+w+1
    F PA194Stepper.stepper ![clock12 k e,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 12,F pairCode ![a4+a4+1,(p+p)+(p+p)]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5
  let scan := F ones ![k,(a6+a6)+(a6+a6)]
  let w := F ones ![k+1,returned e]
  let p := w+w+1
  have hb : before k = scan+scan+1 := by
    dsimp [before,scan,a6,a5,a4,a3,a2,a1,a0]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hr := PA194RollbackCell.modelRollbackBoundary k (a6+a6) (returned e)
  have h4 := PA194ZeroReturnTo12.fourTo12 a4 w
  dsimp only at h4
  have h := zeroRollback k e hz
  rw [hb,(modelOdd scan).1,(modelOdd scan).2] at h
  have hstart : F PA194Stepper.stepper ![clockRollback k e,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 11,F pairCode ![scan,returned e+returned e+1]] := by
    convert h using 1 <;> simp only [add_assoc,add_comm,add_left_comm]
  change F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 11,
    F pairCode ![scan,returned e+returned e+1]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![a6+a6,w+w]] at hr
  change F PA194Stepper.stepper ![modelNumeral M 4,
    F pairCode ![modelNumeral M 11,F pairCode ![a6+a6,w+w]]] = _ at h4
  dsimp only [clock12]
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hstart,hr,h4]
theorem zeroTo14 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    ∃ r : M, returned e = r+r ∧
      let a0 := (1 : M)+(1 : M)+1
      let a1 := a0+a0
      let a2 := a1+a1
      let a3 := a2+a2
      let a4 := a3+a3+1
      let l := a4+a4+1
      let l' := F zeros ![k+1,F zeros ![modelNumeral M 2,l]+F zeros ![modelNumeral M 2,l]]
      F PA194Stepper.stepper ![clock14 k e,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => l'),F parityCode (fun _ => l')+(r+r)+(r+r)]] := by
  obtain ⟨r,hr⟩ := PA194Site27ZeroTo14.returnedEven e
  have h := zeroTo12 k e hz
  refine ⟨r,hr,?_⟩
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let l := a4+a4+1
  let w := F ones ![k+1,r+r]
  rw [hr] at h
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 2) (k+1) l r
  rw [PA194HeaderController.zerosTwo] at hs
  dsimp only [clock14]
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
theorem zeroTo24 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    ∃ r : M, returned e = r+r ∧
      let z := F zeros ![k+1,(1 : M)+(r+r)+(r+r)]
      let x := (z+z)+(z+z)
      let x1 := (1 : M)+x+x
      let t := (1 : M)+x1+x1
      let t1 := t+t
      let t2 := t1+t1
      let t3 := t2+t2
      let t4 := t3+t3
      F PA194Stepper.stepper ![clock24 k e,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  obtain ⟨r,hr,h14⟩ := zeroTo14 k e hz
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let z := F zeros ![k+1,(1 : M)+(r+r)+(r+r)]
  let x := (z+z)+(z+z)
  let x1 := (1 : M)+x+x
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let c16 := ((1 : M)+(k+1))+modelNumeral M 3
  have h16 := PA194ZeroReturnTo16.from14To16 k a4 r
  dsimp only at h16
  rw [(modelOdd a3).1,(modelOdd a3).2] at h16
  have heq : (1 : M)+(1+1)+(x+x)+(x+x) = x1+x1+1 := by
    dsimp [x1]; simp only [add_assoc,add_comm,add_left_comm]
  rw [heq] at h16
  have hone (v : M) : F PA194Stepper.stepper ![(1 : M),v] = F PackedClock.encodedStep (fun _ => v) := by
    rw [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),v] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
  have hrow := PA194Site27ZeroTo24.oneFrom16 a2 x1
  have hrow' : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,F pairCode ![a3,x1+x1+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(x1+x1)+(x1+x1)]] := by
    rw [hone,hrow]
    congr 2
    simp only [add_assoc,add_comm,add_left_comm]
  have h24 := PA194ZeroReturnFrom16.returnFrom16 x1
  dsimp only at h24
  refine ⟨r,hr,?_⟩
  dsimp only [clock24]
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h14,h16,hrow',h24]
theorem zeroBranchWithFile (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M))
    (hf : returned e = F sourceFileCode e) :
    F PA194Stepper.stepper ![clock24 k e,physicalFrame 27 ((k+1)+1) e] =
      physicalFrame 31 ((k+1)+1) e := by
  obtain ⟨r,hr,h⟩ := zeroTo24 k e hz
  let z := F zeros ![k+1,(1 : M)+(r+r)+(r+r)]
  have hp := PA194Path31Header.path31Word z
  dsimp only at hp
  have hgap : F zeros ![(k+1)+1,(1 : M)+(F sourceFileCode e+F sourceFileCode e)] = z+z := by
    rw [←hf,hr]
    have harg : (1 : M)+((r+r)+(r+r)) = (1 : M)+(r+r)+(r+r) := by simp only [add_assoc]
    rw [harg]
    change F zeros ![F addCode ![k+1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelZerosSucc]
  change F PA194Stepper.stepper ![clock24 k e,physicalFrame 27 ((k+1)+1) e] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 31)
      (F zeros ![(k+1)+1,(1 : M)+(F sourceFileCode e+F sourceFileCode e)])]]
  rw [hgap,hp]
  exact h

#print axioms zeroRollback
#print axioms zeroTo12
#print axioms zeroTo14
#print axioms zeroTo24
#print axioms zeroBranchWithFile
end models
end PA194Site27ZeroClockPhysical
