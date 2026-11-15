import PA194Site27PositiveCell
import PA194CarryFile
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site27PositiveSix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site27PositiveCell PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnSix (e : Fin 7 → M) (base file : M) :
    let left := F (PA194CarryFile.leftCode 6) (Fin.cases base e)
    let f1 := F ones ![e 5,(file+file)+(file+file)+1]
    let f2 := F ones ![e 4,(f1+f1)+(f1+f1)+1]
    let f3 := F ones ![e 3,(f2+f2)+(f2+f2)+1]
    let f4 := F ones ![e 2,(f3+f3)+(f3+f3)+1]
    let f5 := F ones ![e 1,(f4+f4)+(f4+f4)+1]
    let f6 := F ones ![e 0,(f5+f5)+(f5+f5)+1]
    let t1 := (1 : M)+(e 5+1)
    let t2 := (1 : M)+(e 4+1)
    let t3 := (1 : M)+(e 3+1)
    let t4 := (1 : M)+(e 2+1)
    let t5 := (1 : M)+(e 1+1)
    let t6 := (1 : M)+(e 0+1)
    F PA194Stepper.stepper ![(((((t1+t2)+t3)+t4)+t5)+t6),
      F pairCode ![modelNumeral M 6,F pairCode ![left+left+1,file+file]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,f6+f6]] := by
  dsimp only
  let x0 := base
  let x1 := F ones ![e 0,(x0+x0+1)+(x0+x0+1)]
  let x2 := F ones ![e 1,(x1+x1+1)+(x1+x1+1)]
  let x3 := F ones ![e 2,(x2+x2+1)+(x2+x2+1)]
  let x4 := F ones ![e 3,(x3+x3+1)+(x3+x3+1)]
  let x5 := F ones ![e 4,(x4+x4+1)+(x4+x4+1)]
  let x6 := F ones ![e 5,(x5+x5+1)+(x5+x5+1)]
  let f1 := F ones ![e 5,(file+file)+(file+file)+1]
  let f2 := F ones ![e 4,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![e 3,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![e 2,(f3+f3)+(f3+f3)+1]
  let f5 := F ones ![e 1,(f4+f4)+(f4+f4)+1]
  let f6 := F ones ![e 0,(f5+f5)+(f5+f5)+1]
  let t1 := (1 : M)+(e 5+1)
  let t2 := (1 : M)+(e 4+1)
  let t3 := (1 : M)+(e 3+1)
  let t4 := (1 : M)+(e 2+1)
  let t5 := (1 : M)+(e 1+1)
  let t6 := (1 : M)+(e 0+1)
  have hl : F (PA194CarryFile.leftCode 6) (Fin.cases base e) = x6 := by
    dsimp only [x6,x5,x4,x3,x2,x1,x0]
    simp only [PA194CarryFile.modelLeftSucc,PA194CarryFile.modelLeftZero,PA194CarryFile.modelAdvance]
    rfl
  rw [hl]
  have h1 := returnCell (e 5) x5 file
  have h2 := returnCell (e 4) x4 f1
  have h3 := returnCell (e 3) x3 f2
  have h4 := returnCell (e 2) x2 f3
  have h5 := returnCell (e 1) x1 f4
  have h6 := returnCell (e 0) x0 f5
  dsimp only at h1 h2 h3 h4 h5 h6
  change F PA194Stepper.stepper ![F addCode ![((((t1+t2)+t3)+t4)+t5),t6],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![t6,F PA194Stepper.stepper ![F addCode ![(((t1+t2)+t3)+t4),t5],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![t6,F PA194Stepper.stepper ![t5,F PA194Stepper.stepper ![F addCode ![((t1+t2)+t3),t4],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![t6,F PA194Stepper.stepper ![t5,F PA194Stepper.stepper ![t4,F PA194Stepper.stepper ![F addCode ![(t1+t2),t3],_]]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![t6,F PA194Stepper.stepper ![t5,F PA194Stepper.stepper ![t4,F PA194Stepper.stepper ![t3,F PA194Stepper.stepper ![F addCode ![t1,t2],_]]]]] = _
  rw [PA194StepperCompose.modelStepperCompose,h1,h2,h3,h4,h5,h6]
#print axioms returnSix
end models
end PA194Site27PositiveSix
