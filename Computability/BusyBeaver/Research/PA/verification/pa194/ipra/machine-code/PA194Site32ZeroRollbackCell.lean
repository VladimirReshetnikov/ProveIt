import PA194CarryEightAppendZero
import PA194RollbackFile
import PA194Site27BranchRows
import PA194Site27ZeroTo11
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroRollbackCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194RegisterFile PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem rollback (base a b c d e f g h spare suffix : M) :
    let t := F ones ![spare+1,suffix]
    let q := F ones ![(0 : M),t+t]
    let eight : Fin 9 → M := ![a,b,c,d,e,f,g,h,(q+q)+(q+q)]
    let nine : Fin 10 → M := ![a,b,c,d,e,f,g,h,0,(q+q)+(q+q)]
    let carried := F (PA194CarryFile.leftCode 8) (Fin.cases base eight)
    let z := carried+carried+1
    let returned := F (PA194ReturnFile.returnCode 9) (Fin.cases (t+t) nine)
    let cost := F (PA194CarryFile.costCode 9) nine
    F PA194Stepper.stepper ![F addCode ![F addCode ![modelNumeral M 1,modelNumeral M 2],cost],
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => base),F parityCode (fun _ => base)+returned+returned]] := by
  dsimp only
  let t := F ones ![spare+1,suffix]
  let u := F ones ![spare,suffix]
  let q := F ones ![(0 : M),t+t]
  let eight : Fin 9 → M := ![a,b,c,d,e,f,g,h,(q+q)+(q+q)]
  let nine : Fin 10 → M := ![a,b,c,d,e,f,g,h,0,(q+q)+(q+q)]
  let carried := F (PA194CarryFile.leftCode 8) (Fin.cases base eight)
  let z := carried+carried+1
  have ht : t=u+u+1 := by
    dsimp only [t,u]
    rw [show spare+1 = F Code.succ (fun _ => spare) from modelAddOne _,modelOnesSucc]
  have hrow := PA194Site27BranchRows.zeroRow z t
  have h11 := PA194Site27ZeroTo11.fiveTo11 z u
  dsimp only at h11
  rw [←ht] at h11
  have hc := PA194CarryEightAppendZero.eightThenZero base a b c d e f g h ((q+q)+(q+q))
  dsimp only at hc
  change F (PA194CarryFile.leftCode 9) (Fin.cases base nine) = z+z at hc
  have hr := PA194RollbackFile.modelRollbackPrefix 9 nine base (t+t)
  dsimp only at hr
  rw [hc,(modelDouble z).1,(modelDouble z).2] at hr
  simp only [zero_add] at hr
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hrow,h11,hr]
#print axioms rollback
end models
end PA194Site32ZeroRollbackCell
