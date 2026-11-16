import PA194AX11HCompare
import PA194AX11HCopyCombined
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194AX11HCompareExit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194AX11HCompareRows
open Classical
open PA194ModelMPCompare (values)
open PA194AX11HCompare (Reaches append oneStep)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact full file after comparison and conditional success copy. -/
noncomputable def result (a : Fin 11 → M) : Fin 11 → M :=
  if a 5 = a 6 then Function.update (values a 0 0) 1 (a 1+a 4) else values a 0 0

/-- Complete comparison/return branch, with no assumption on the two
model-valued quantities being compared. -/
theorem compareAndReturn (a : Fin 11 → M) (tail : M) :
    Reaches (sourceState 3642 a tail) (sourceState 25 (result a) tail) := by
  by_cases he : a 5 = a 6
  · have h := PA194AX11HCompare.compareEqual a tail he
    have hc := copySuccess (values a 0 0) tail (by simp [values])
    have hout : Function.update (values a 0 0) 1 ((values a 0 0) 1+(values a 0 0) 4) = result a := by
      simp [result,he,values]
    rw [hout] at hc
    have hj := PA194AX11HSourceAt.sourceJump 3659 25 (by decide) s3659 (result a) tail
    exact append (append h hc) (oneStep hj)
  · have h := PA194AX11HCompare.compare a tail
    rw [if_neg he] at h
    have hr : result a = values a 0 0 := by simp [result,he]
    rw [←hr] at h
    have hj := PA194AX11HSourceAt.sourceJump 3659 25 (by decide) s3659 (result a) tail
    exact append h (oneStep hj)

#print axioms copySuccess
#print axioms compareAndReturn
end models
end PA194AX11HCompareExit
