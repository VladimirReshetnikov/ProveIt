import PA194AX11HCompare
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194AX11HCompareReturn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive
open PA194ModelMPCompare (values)
open PA194AX11HCompareRows
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

/-- The exact comparison/return source path when equality entails D=0.
The hypothesis is not needed in the unequal branch. -/
theorem compareAndReturn (a : Fin 11 → M) (tail : M) (hzero : a 5 = a 6 → a 4 = 0) :
    Reaches (sourceState 3642 a tail) (sourceState 25 (values a 0 0) tail) := by
  let b := values a 0 0
  have hj := PA194AX11HSourceAt.sourceJump 3659 25 (by decide) s3659 b tail
  by_cases he : a 5 = a 6
  · have hc := PA194AX11HCompare.compareEqual a tail he
    have hd : regsOfArgs b 4 = 0 := by simp [b,values,regsOfArgs,hzero he]
    have hx : regsOfArgs b 6 = 0 := by simp [b,values,regsOfArgs]
    have h1 := PA194AX11HSourceAt.sourceDecZero 3652 3656 4 (some 3653) (by decide) s3652 b tail hd
    have h2 := PA194AX11HSourceAt.sourceDecZero 3656 3659 6 (some 3657) (by decide) s3656 b tail hx
    exact append (append (append hc (oneStep h1)) (oneStep h2)) (oneStep hj)
  · have hc := PA194AX11HCompare.compare a tail
    rw [if_neg he] at hc
    exact append hc (oneStep hj)

#print axioms compareAndReturn
end models
end PA194AX11HCompareReturn
