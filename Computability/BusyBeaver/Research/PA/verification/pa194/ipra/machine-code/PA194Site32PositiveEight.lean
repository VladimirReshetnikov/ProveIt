import PA194Site27PositiveSix
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32PositiveEight
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site27PositiveCell PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnEight (e : Fin 9 → M) (base file : M) :
    let left := F (PA194CarryFile.leftCode 8) (Fin.cases base e)
    let f1 := F ones ![e 7,(file+file)+(file+file)+1]
    let f2 := F ones ![e 6,(f1+f1)+(f1+f1)+1]
    let f3 := F ones ![e 5,(f2+f2)+(f2+f2)+1]
    let f4 := F ones ![e 4,(f3+f3)+(f3+f3)+1]
    let f5 := F ones ![e 3,(f4+f4)+(f4+f4)+1]
    let f6 := F ones ![e 2,(f5+f5)+(f5+f5)+1]
    let f7 := F ones ![e 1,(f6+f6)+(f6+f6)+1]
    let f8 := F ones ![e 0,(f7+f7)+(f7+f7)+1]
    let t1 := (1 : M)+(e 7+1)
    let t2 := (1 : M)+(e 6+1)
    let t3 := (1 : M)+(e 5+1)
    let t4 := (1 : M)+(e 4+1)
    let t5 := (1 : M)+(e 3+1)
    let t6 := (1 : M)+(e 2+1)
    let t7 := (1 : M)+(e 1+1)
    let t8 := (1 : M)+(e 0+1)
    F PA194Stepper.stepper ![(((((((t1+t2)+t3)+t4)+t5)+t6)+t7)+t8),
      F pairCode ![modelNumeral M 6,F pairCode ![left+left+1,file+file]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,f8+f8]] := by
  dsimp only
  let x1 := F ones ![e 0,(base+base+1)+(base+base+1)]
  let x2 := F ones ![e 1,(x1+x1+1)+(x1+x1+1)]
  let es : Fin 7 → M := fun i => e i.succ.succ
  let f1 := F ones ![e 7,(file+file)+(file+file)+1]
  let f2 := F ones ![e 6,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![e 5,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![e 4,(f3+f3)+(f3+f3)+1]
  let f5 := F ones ![e 3,(f4+f4)+(f4+f4)+1]
  let f6 := F ones ![e 2,(f5+f5)+(f5+f5)+1]
  let f7 := F ones ![e 1,(f6+f6)+(f6+f6)+1]
  let t1 := (1 : M)+(e 7+1)
  let t2 := (1 : M)+(e 6+1)
  let t3 := (1 : M)+(e 5+1)
  let t4 := (1 : M)+(e 4+1)
  let t5 := (1 : M)+(e 3+1)
  let t6 := (1 : M)+(e 2+1)
  let t7 := (1 : M)+(e 1+1)
  let t8 := (1 : M)+(e 0+1)
  let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
  have hl : F (PA194CarryFile.leftCode 8) (Fin.cases base e) = F (PA194CarryFile.leftCode 6) (Fin.cases x2 es) := by
    dsimp only [x2,x1,es]
    simp only [PA194CarryFile.modelLeftSucc,PA194CarryFile.modelAdvance,Fin.cases_zero,Fin.cases_succ]
    rfl
  have h6 := PA194Site27PositiveSix.returnSix es x2 file
  dsimp only at h6
  change F PA194Stepper.stepper ![c6,F pairCode ![modelNumeral M 6,
    F pairCode ![F (PA194CarryFile.leftCode 6) (Fin.cases x2 es)+F (PA194CarryFile.leftCode 6) (Fin.cases x2 es)+1,file+file]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![x2+x2+1,f6+f6]] at h6
  have h7 := returnCell (e 1) x1 f6
  have h8 := returnCell (e 0) base f7
  dsimp only at h7 h8
  rw [hl]
  change F PA194Stepper.stepper ![F addCode ![F addCode ![c6,t7],t8],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![t8,F PA194Stepper.stepper ![F addCode ![c6,t7],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h6,h7,h8]
#print axioms returnEight
end models
end PA194Site32PositiveEight
