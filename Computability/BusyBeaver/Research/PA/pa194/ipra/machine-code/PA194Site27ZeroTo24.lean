import PA194Site27ZeroTo14
import PA194ZeroReturnTo16
import PA194ZeroReturnFrom16
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroTo24
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194SourceSite25Physical PA194Site27ZeroRollback PA194ReturnFile
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem oneFrom16 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  have h := PA194LeftOneWriteOne.leftOneWriteOne 16 16 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem zeroTo24 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    ∃ r clock : M, returned e = r+r ∧
      let z := F zeros ![k+1,(1 : M)+(r+r)+(r+r)]
      let x := (z+z)+(z+z)
      let x1 := (1 : M)+x+x
      let t := (1 : M)+x1+x1
      let t1 := t+t
      let t2 := t1+t1
      let t3 := t2+t2
      let t4 := t3+t3
      F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  obtain ⟨r,c,hr,h14⟩ := PA194Site27ZeroTo14.zeroTo14 k e hz
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
  have hrow := oneFrom16 a2 x1
  have hrow' : F PA194Stepper.stepper ![(1 : M),F pairCode ![modelNumeral M 16,F pairCode ![a3,x1+x1+1]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(x1+x1)+(x1+x1)]] := by
    rw [hone,hrow]
    congr 2
    simp only [add_assoc,add_comm,add_left_comm]
  have h24 := PA194ZeroReturnFrom16.returnFrom16 x1
  dsimp only at h24
  refine ⟨r,F addCode ![F addCode ![F addCode ![c,c16],(1 : M)],modelNumeral M 3+rc],hr,?_⟩
  dsimp only
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h14,h16,hrow',h24]
#print axioms oneFrom16
#print axioms zeroTo24
end models
end PA194Site27ZeroTo24
