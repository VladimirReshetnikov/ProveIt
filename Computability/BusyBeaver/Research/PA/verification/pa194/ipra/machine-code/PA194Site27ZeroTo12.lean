import PA194Site27ZeroRollback
import PA194ZeroReturnTo12
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroTo12
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194SourceSite25Physical PA194Site27ZeroRollback
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroTo12 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let w := F ones ![k+1,returned e]
    let p := w+w+1
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
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
  obtain ⟨c,h⟩ := zeroRollback k e hz
  rw [hb,(modelOdd scan).1,(modelOdd scan).2] at h
  have hstart : F PA194Stepper.stepper ![c,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 11,F pairCode ![scan,returned e+returned e+1]] := by
    convert h using 1 <;> simp only [add_assoc,add_comm,add_left_comm]
  change F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 11,
    F pairCode ![scan,returned e+returned e+1]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![a6+a6,w+w]] at hr
  change F PA194Stepper.stepper ![modelNumeral M 4,
    F pairCode ![modelNumeral M 11,F pairCode ![a6+a6,w+w]]] = _ at h4
  refine ⟨F addCode ![F addCode ![c,k+1],modelNumeral M 4],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hstart,hr,h4]
#print axioms zeroTo12
end models
end PA194Site27ZeroTo12
