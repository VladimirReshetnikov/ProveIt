import PA194Site48PositiveFour
import PA194Site27BranchRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site48PositiveReturnCell
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
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem returnPositive (e : Fin 4 → M) (base m tail : M) :
    let q := F ones ![m+1,tail]
    let vec : Fin 5 → M := ![e 0,e 1,e 2,e 3,(q+q)+(q+q)]
    let left := F (PA194CarryFile.leftCode 4) (Fin.cases base vec)
    let z := left+left+1
    let f1 := F ones ![e 3,(q+q)+(q+q)+1]
    let f2 := F ones ![e 2,(f1+f1)+(f1+f1)+1]
    let f3 := F ones ![e 1,(f2+f2)+(f2+f2)+1]
    let f4 := F ones ![e 0,(f3+f3)+(f3+f3)+1]
    let t1 := (1 : M)+(e 3+1)
    let t2 := (1 : M)+(e 2+1)
    let t3 := (1 : M)+(e 1+1)
    let t4 := (1 : M)+(e 0+1)
    let c := (((t1+t2)+t3)+t4)
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 1,c],
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,f4+f4]] := by
  dsimp only
  let q := F ones ![m+1,tail]
  let vec : Fin 5 → M := ![e 0,e 1,e 2,e 3,(q+q)+(q+q)]
  let left := F (PA194CarryFile.leftCode 4) (Fin.cases base vec)
  let z := left+left+1
  have hq : q = F ones ![m,tail]+F ones ![m,tail]+1 := by
    dsimp only [q]
    rw [show m+1 = F Code.succ (fun _ => m) from modelAddOne _,modelOnesSucc]
  have hrow := PA194Site27BranchRows.positiveRow z m tail
  dsimp only at hrow
  rw [←hq] at hrow
  let f1 := F ones ![e 3,(q+q)+(q+q)+1]
  let f2 := F ones ![e 2,(f1+f1)+(f1+f1)+1]
  let f3 := F ones ![e 1,(f2+f2)+(f2+f2)+1]
  let f4 := F ones ![e 0,(f3+f3)+(f3+f3)+1]
  let t1 := (1 : M)+(e 3+1)
  let t2 := (1 : M)+(e 2+1)
  let t3 := (1 : M)+(e 1+1)
  let t4 := (1 : M)+(e 0+1)
  let c := ((t1+t2)+t3)+t4
  have h4 := PA194Site48PositiveFour.returnFour vec base q
  dsimp only at h4
  change F PA194Stepper.stepper ![c,F pairCode ![modelNumeral M 6,F pairCode ![z,q+q]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![base+base+1,f4+f4]] at h4
  rw [PA194StepperCompose.modelStepperCompose,hrow]
  exact h4
#print axioms returnPositive
end models
end PA194Site48PositiveReturnCell
