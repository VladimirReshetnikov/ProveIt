import PA194ModelMPCompare
import PA194ModelMPTransfer

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ModelMPGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ModelMPDrain
open PA194ModelMPCompare PA194ModelMPTransfer PA194MPLiteralRows

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

theorem compareEqual (a : Fin 11 → M) (tail : M) (h : a 5 = a 6) :
    ReachesPositive (sourceState 3624 a tail) (sourceState 3634 (values a 0 0) tail) := by
  have hc := comparePrefix a tail (a 5) le_rfl (le_of_eq h)
  have he : rest a (a 5) = values a 0 0 := by unfold rest; rw [h,subSelf]
  rw [he] at hc
  let b := values a 0 0
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = 0 := by simp [b,values,regsOfArgs]
  have h1 := sourceDecZero 3624 3628 5 (some 3625) (by decide) s3624 b tail h5
  have h2 := sourceDecZero 3628 3634 6 (some 3629) (by decide) s3628 b tail h6
  exact appendPositive (append hc (oneStep h1).reaches) (oneStep h2)

theorem compareLess (a : Fin 11 → M) (tail : M) (h : a 5 < a 6) :
    ReachesPositive (sourceState 3624 a tail) (sourceState 3660 (values a 0 0) tail) := by
  have hc := comparePrefix a tail (a 5) le_rfl (le_of_lt h)
  obtain ⟨x,hx,_⟩ := remainderSucc (a 6) (a 5) h
  let b := values a 0 (x+1)
  let c := Function.update b 6 x
  have he : rest a (a 5) = b := by unfold rest b; rw [subSelf,hx]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = x+1 := by simp [b,values,regsOfArgs]
  have h1 := sourceDecZero 3624 3628 5 (some 3625) (by decide) s3624 b tail h5
  have h2 := sourceDecPositive 3628 3629 6 (some 3634) (by decide) s3628 b tail x h6
  have h3 := cleanup c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i; fin_cases i <;> simp [c,b,values]
  rw [hend] at h3
  exact appendPositive (append (append hc (oneStep h1).reaches) (oneStep h2).reaches) h3

theorem compareGreater (a : Fin 11 → M) (tail : M) (h : a 6 < a 5) :
    ReachesPositive (sourceState 3624 a tail) (sourceState 3660 (values a 0 0) tail) := by
  have hc := comparePrefix a tail (a 6) (le_of_lt h) le_rfl
  obtain ⟨v,hv,_⟩ := remainderSucc (a 5) (a 6) h
  let b := values a (v+1) 0
  let c := Function.update b 5 v
  have he : rest a (a 6) = b := by unfold rest b; rw [subSelf,hv]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = v+1 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs c 6 = 0 := by simp [c,b,values,regsOfArgs]
  have h1 := sourceDecPositive 3624 3625 5 (some 3628) (by decide) s3624 b tail v h5
  have h2 := sourceDecZero 3625 3627 6 (some 3626) (by decide) s3625 c tail h6
  have h3 := sourceJump 3627 3629 (by decide) s3627 c tail
  have h4 := cleanup c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i; fin_cases i <;> simp [c,b,values]
  rw [hend] at h4
  exact appendPositive (append (append (append hc (oneStep h1).reaches) (oneStep h2).reaches)
    (oneStep h3).reaches) h4

theorem compare (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState 3624 a tail)
      (sourceState (if a 5 = a 6 then 3634 else 3660) (values a 0 0) tail) := by
  rcases lt_trichotomy (a 5) (a 6) with h | h | h
  · rw [if_neg (ne_of_lt h)]
    exact compareLess a tail h
  · rw [if_pos h]
    exact compareEqual a tail h
  · rw [if_neg (ne_of_gt h)]
    exact compareGreater a tail h

def clear (a : Fin 11 → M) : Fin 11 → M := values (Function.update a 1 0) 0 0

/-- The equality guard compares T with H and clears T, H and X. -/
theorem guard (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) :
    ReachesPositive (sourceState 3621 a tail)
      (sourceState (if a 1 = a 5 then 3634 else 3660) (clear a) tail) := by
  have rows : TransferRows 3621 3624 1 6 := ⟨by decide,s3621,s3622,s3623⟩
  have h := transfer 3621 3624 1 6 rows (by decide) a tail
  let b := transferArgs a 1 6
  have hc := compare b tail
  have hb1 : b 5 = a 5 := by simp [b,transferArgs,location]
  have hb2 : b 6 = a 1 := by simp [b,transferArgs,location,hX]
  have hb3 : values b 0 0 = clear a := by
    funext i
    fin_cases i <;> simp [b,transferArgs,location,values,clear]
  rw [hb1,hb2,hb3] at hc
  have he : (if a 5 = a 1 then 3634 else 3660) = (if a 1 = a 5 then 3634 else 3660) := by
    by_cases hz : a 1 = a 5
    · rw [if_pos hz,if_pos hz.symm]
    · rw [if_neg hz,if_neg (Ne.symm hz)]
  rw [he] at hc
  exact appendPositive h.reaches hc

#print axioms guard
end models
end PA194ModelMPGuard
