import PA194Site27ZeroExact
import PA194CarryAppendZero
import PA194RollbackFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroRollback
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open BinaryTapeCodes PA194ReturnFile PRAModelIOpenPairing PA194BinaryDouble PA194SourceSite25Physical PA194Site27ZeroExact
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def before (k : M) : M :=
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5
  F ones ![k+1,(a6+a6)+(a6+a6)]
noncomputable def tailWord (e : Fin 11 → M) : M :=
  let v := physicalArgs e
  let e1 : Fin 10 → M := fun j => v j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
noncomputable def seven (e : Fin 11 → M) : Fin 8 → M :=
  let v := physicalArgs e
  let t := tailWord e
  let q := F ones ![(0 : M),t+t]
  ![v 0,v 1,v 2,v 3,v 4,v 5,0,(q+q)+(q+q)]
noncomputable def returned (e : Fin 11 → M) : M :=
  F (PA194ReturnFile.returnCode 7) (Fin.cases (tailWord e+tailWord e) (seven e))

theorem carriedIsSeven (k : M) (e : Fin 11 → M) :
    let z := selectedCarry k e + selectedCarry k e + 1
    F (PA194CarryFile.leftCode 7) (Fin.cases (before k) (seven e)) = z+z := by
  let v := physicalArgs e
  let t := tailWord e
  let q := F ones ![(0 : M),t+t]
  have h := PA194CarryAppendZero.sixThenZero (before k) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) ((q+q)+(q+q))
  dsimp only at h ⊢
  exact h

theorem zeroRollback (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
        F parityCode (fun _ => before k)+returned e+returned e]] := by
  let t := tailWord e
  let z := selectedCarry k e + selectedCarry k e + 1
  obtain ⟨clock,hstart⟩ := PA194Site27ZeroExact.zeroTo11Exact k e hz
  dsimp only at hstart
  have hroll := PA194RollbackFile.modelRollbackPrefix 7 (seven e) (before k) (t+t)
  dsimp only at hroll
  have hc := carriedIsSeven k e
  dsimp only at hc
  rw [hc,(modelDouble z).1,(modelDouble z).2] at hroll
  simp only [zero_add] at hroll
  change F PA194Stepper.stepper ![F (PA194CarryFile.costCode 7) (seven e),
    F pairCode ![modelNumeral M 11,F pairCode ![z,(t+t)+(t+t)]]] = _ at hroll
  refine ⟨F addCode ![clock,F (PA194CarryFile.costCode 7) (seven e)],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hstart]
  exact hroll
#print axioms carriedIsSeven
#print axioms zeroRollback
end models
end PA194Site27ZeroRollback
