import PA194ProgramCompare
import PA194ProgramTransfer

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ProgramGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194ProgramDrain PA194ProgramCompare PA194ProgramTransfer
open PA194ModelMPDrain (location subSelf)
open PA194ModelMPTransfer (transferArgs)

structure Rows (program : Program) (base : Nat) : Prop where
  transfer : TransferRows program base (base+3) 1 6
  compare : PA194ProgramCompare.Rows program (base+3) (base+39)

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

theorem compareEqual (program : Program) (base : Nat) (rows : Rows program base) (a : Fin 11 → M) (tail : M) (h : a 5 = a 6) :
    ReachesPositive program (sourceState (base+3) a tail) (sourceState (base+13) (values a 0 0) tail) := by
  have hc := PA194ProgramCompare.comparePrefix program (base+3) (base+39) rows.compare a tail (a 5) le_rfl (le_of_eq h)
  have he : rest a (a 5) = values a 0 0 := by unfold rest; rw [h,subSelf]
  rw [he] at hc
  let b := values a 0 0
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = 0 := by simp [b,values,regsOfArgs]
  have h1 := sourceDecZero program (base+3) (base+7) 5 (some (base+4)) (by have := rows.compare.valid; omega) rows.compare.htest b tail h5
  have h2 := sourceDecZero program (base+7) (base+13) 6 (some (base+8)) (by have := rows.compare.valid; omega) rows.compare.equalTest b tail h6
  exact appendPositive program (append program hc (oneStep program h1).reaches) (oneStep program h2)

theorem compareLess (program : Program) (base : Nat) (rows : Rows program base) (a : Fin 11 → M) (tail : M) (h : a 5 < a 6) :
    ReachesPositive program (sourceState (base+3) a tail) (sourceState (base+39) (values a 0 0) tail) := by
  have hc := PA194ProgramCompare.comparePrefix program (base+3) (base+39) rows.compare a tail (a 5) le_rfl (le_of_lt h)
  obtain ⟨x,hx,_⟩ := remainderSucc (a 6) (a 5) h
  let b := values a 0 (x+1)
  let c := Function.update b 6 x
  have he : rest a (a 5) = b := by unfold rest b; rw [subSelf,hx]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = x+1 := by simp [b,values,regsOfArgs]
  have h1 := sourceDecZero program (base+3) (base+7) 5 (some (base+4)) (by have := rows.compare.valid; omega) rows.compare.htest b tail h5
  have h2 := sourceDecPositive program (base+7) (base+8) 6 (some (base+13)) (by have := rows.compare.valid; omega) rows.compare.equalTest b tail x h6
  have h3 := PA194ProgramCompare.cleanup program (base+3) (base+39) rows.compare c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i; fin_cases i <;> simp [c,b,values]
  rw [hend] at h3
  exact appendPositive program (append program (append program hc (oneStep program h1).reaches) (oneStep program h2).reaches) h3

theorem compareGreater (program : Program) (base : Nat) (rows : Rows program base) (a : Fin 11 → M) (tail : M) (h : a 6 < a 5) :
    ReachesPositive program (sourceState (base+3) a tail) (sourceState (base+39) (values a 0 0) tail) := by
  have hc := PA194ProgramCompare.comparePrefix program (base+3) (base+39) rows.compare a tail (a 6) (le_of_lt h) le_rfl
  obtain ⟨v,hv,_⟩ := remainderSucc (a 5) (a 6) h
  let b := values a (v+1) 0
  let c := Function.update b 5 v
  have he : rest a (a 6) = b := by unfold rest b; rw [subSelf,hv]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = v+1 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs c 6 = 0 := by simp [c,b,values,regsOfArgs]
  have h1 := sourceDecPositive program (base+3) (base+4) 5 (some (base+7)) (by have := rows.compare.valid; omega) rows.compare.htest b tail v h5
  have h2 := sourceDecZero program (base+4) (base+6) 6 (some (base+5)) (by have := rows.compare.valid; omega) rows.compare.xtest c tail h6
  have h3 := sourceJump program (base+6) (base+8) (by have := rows.compare.valid; omega) rows.compare.toClean c tail
  have h4 := PA194ProgramCompare.cleanup program (base+3) (base+39) rows.compare c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i; fin_cases i <;> simp [c,b,values]
  rw [hend] at h4
  exact appendPositive program (append program (append program (append program hc (oneStep program h1).reaches) (oneStep program h2).reaches)
    (oneStep program h3).reaches) h4

theorem compare (program : Program) (base : Nat) (rows : Rows program base) (a : Fin 11 → M) (tail : M) :
    ReachesPositive program (sourceState (base+3) a tail)
      (sourceState (if a 5 = a 6 then (base+13) else (base+39)) (values a 0 0) tail) := by
  rcases lt_trichotomy (a 5) (a 6) with h | h | h
  · rw [if_neg (ne_of_lt h)]
    exact compareLess program base rows a tail h
  · rw [if_pos h]
    exact compareEqual program base rows a tail h
  · rw [if_neg (ne_of_gt h)]
    exact compareGreater program base rows a tail h

def clear (a : Fin 11 → M) : Fin 11 → M := values (Function.update a 1 0) 0 0

/-- The equality guard compares T with H and clears T, H and X. -/
theorem guard (program : Program) (base : Nat) (rows : Rows program base) (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) :
    ReachesPositive program (sourceState (base+0) a tail)
      (sourceState (if a 1 = a 5 then (base+13) else (base+39)) (clear a) tail) := by
  have h := transfer program (base+0) (base+3) 1 6 rows.transfer (by decide) a tail
  let b := transferArgs a 1 6
  have hc := compare program base rows b tail
  have hb1 : b 5 = a 5 := by simp [b,transferArgs,location]
  have hb2 : b 6 = a 1 := by simp [b,transferArgs,location,hX]
  have hb3 : values b 0 0 = clear a := by
    funext i
    fin_cases i <;> simp [b,transferArgs,location,values,clear]
  rw [hb1,hb2,hb3] at hc
  have he : (if a 5 = a 1 then (base+13) else (base+39)) = (if a 1 = a 5 then (base+13) else (base+39)) := by
    by_cases hz : a 1 = a 5
    · rw [if_pos hz,if_pos hz.symm]
    · rw [if_neg hz,if_neg (Ne.symm hz)]
  rw [he] at hc
  exact appendPositive program h.reaches hc

#print axioms guard
end models
end PA194ProgramGuard
