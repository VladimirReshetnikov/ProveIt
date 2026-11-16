import PA194ModelMPDrain
import PA194MPLiteralRows3554
import PA194MPLiteralRows3621

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1300000
set_option linter.unusedSectionVars false

namespace PA194ModelMPCopy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194MPLiteralRows

structure Rows (base : Nat) : Prop where
  valid : base+6 < 3673
  input : row base = some (.dec 4 (some (base+4)) (some (base+1)))
  increaseT : row (base+1) = some (.inc 1 (some (base+2)))
  increaseX : row (base+2) = some (.inc 6 (some (base+3)))
  repeatD : row (base+3) = some (.jump (some base))
  scratch : row (base+4) = some (.dec 6 (some (base+7)) (some (base+5)))
  increaseD : row (base+5) = some (.inc 4 (some (base+6)))
  repeatX : row (base+6) = some (.jump (some (base+4)))

theorem entryRows : Rows 3587 :=
  ⟨by decide,s3587,s3588,s3589,s3590,s3591,s3592,s3593⟩

theorem successRows : Rows 3653 :=
  ⟨by decide,s3653,s3654,s3655,s3656,s3657,s3658,s3659⟩

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

/-- Add the preserved offset register into T and restore the scratch register. -/
theorem copy (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail : M)
    (hX : a 6 = 0) :
    ReachesPositive (sourceState base a tail)
      (sourceState (base+7) (Function.update a 1 (a 1+a 4)) tail) := by
  let mid := Function.update (Function.update (Function.update a 4 (0 : M)) 1 (a 1+a 4)) 6 (a 4)
  have path1 : Increments base (base+1) [1,6] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.increaseT
      (.inc _ _ _ _ (by have := rows.valid; omega) rows.increaseX
        (.jump _ (by have := rows.valid; omega) rows.repeatD))
  have h1 := drain base (base+1) (base+4) 4 [1,6] (by have := rows.valid; omega)
    rows.input path1 (by decide) a tail
  have mid_eq : argsAfter a 4 [1,6] (a (location 4)) = mid := by
    funext i
    fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [mid_eq] at h1
  have path2 : Increments (base+4) (base+5) [4] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.increaseD
      (.jump _ rows.valid rows.repeatX)
  have h2 := drain (base+4) (base+5) (base+7) 6 [4] (by have := rows.valid; omega)
    rows.scratch path2 (by decide) mid tail
  have final_eq : argsAfter mid 6 [4] (mid (location 6)) = Function.update a 1 (a 1+a 4) := by
    funext i
    fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [final_eq] at h2
  exact appendPositive h1.reaches h2

#print axioms copy
end models
end PA194ModelMPCopy
