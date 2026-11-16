import PA194ModelMPDrain
import PA194MPLiteralRows3621

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ModelMPCompare
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194MPLiteralRows

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

def values (a : Fin 11 → M) (h x : M) : Fin 11 → M :=
  Function.update (Function.update a 5 h) 6 x

noncomputable def rest (a : Fin 11 → M) (j : M) : Fin 11 → M :=
  values a (F subCode ![a 5,j]) (F subCode ![a 6,j])

theorem remainderSucc (v j : M) (h : j < v) :
    ∃ p : M, F subCode ![v,j] = p+1 ∧ F subCode ![v,j+1] = p := by
  obtain ⟨p,hp⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp h)
  refine ⟨p,?_,?_⟩
  · rw [hp,show (j+1)+p = j+(p+1) by ac_rfl]
    exact modelSubAdd j (p+1)
  · rw [hp]
    exact modelSubAdd (j+1) p

theorem restDef (a : Fin 11 → M) (i : Fin 11) :
    𝚺₁-Function₁ (fun j => rest a j i) := by
  unfold rest values
  by_cases h6 : i = 6
  · simp only [h6,Function.update_self]
    exact subByDef _
  · by_cases h5 : i = 5
    · simp only [Function.update_of_ne h6,h5,Function.update_self]
      exact subByDef _
    · simp only [Function.update_of_ne h6,Function.update_of_ne h5]
      definability

theorem comparePrefix (a : Fin 11 → M) (tail k : M) (hh : k ≤ a 5) (hx : k ≤ a 6) :
    Reaches (sourceState 3624 a tail) (sourceState 3624 (rest a k) tail) := by
  let frame := fun j => sourceState 3624 (rest a j) tail
  have hstep (j : M) (hj : j < k) : Reaches (frame j) (frame (j+1)) := by
    obtain ⟨h,h0,h1⟩ := remainderSucc (a 5) j (lt_of_lt_of_le hj hh)
    obtain ⟨x,x0,x1⟩ := remainderSucc (a 6) j (lt_of_lt_of_le hj hx)
    let curr := rest a j
    let an := Function.update curr 5 h
    let bn := Function.update an 6 x
    have hcurr : curr 5 = h+1 := by simp [curr,rest,values,h0]
    have xcurr : an 6 = x+1 := by simp [an,curr,rest,values,x0]
    have hs := sourceDecPositive 3624 3625 5 (some 3628) (by decide) s3624 curr tail h hcurr
    have ht := sourceDecPositive 3625 3626 6 (some 3627) (by decide) s3625 an tail x xcurr
    have hu := sourceJump 3626 3624 (by decide) s3626 bn tail
    have hb : bn = rest a (j+1) := by
      funext i
      fin_cases i <;> simp [bn,an,curr,rest,values,h1,x1]
    change Reaches (frame j) (sourceState 3624 (rest a (j+1)) tail)
    rw [←hb]
    exact append (append (oneStep hs).reaches (oneStep ht).reaches) (oneStep hu).reaches
  have h := runMany frame k (frameDef 3624 (fun i j => rest a j i) tail (restDef a)) hstep k le_rfl
  have hz : rest a 0 = a := by
    funext i
    fin_cases i <;> simp [rest,values] <;> exact PRASubtraction.modelSubZero _
  change Reaches (sourceState 3624 (rest a 0) tail) (sourceState 3624 (rest a k) tail) at h
  rwa [hz] at h

theorem emptyArgs (a : Fin 11 → M) (r : Fin 9) (j : M) :
    argsAfter a r [] j = Function.update a (location r) (F subCode ![a (location r),j]) := by
  funext i
  by_cases h : i = location r
  · simp [argsAfter,h]
  · simp [argsAfter,h,tally,show modelNumeral M 0 = (0:M) from rfl]

theorem drainX (a : Fin 11 → M) (tail : M) (hz : a 5 = 0) :
    ReachesPositive (sourceState 3631 a tail) (sourceState 3660 (Function.update a 6 0) tail) := by
  let mem := fun j => Function.update a 6 (F subCode ![a 6,j])
  let frame := fun j => sourceState 3631 (mem j) tail
  have hm (i : Fin 11) : 𝚺₁-Function₁ (fun j => mem j i) := by
    have he : (fun j : M => mem j i) = fun j => argsAfter a 6 [] j i := by
      funext j
      rw [emptyArgs]
      rfl
    rw [he]
    exact partialDef a 6 [] i
  have hs (j : M) (hj : j < a 6) : Reaches (frame j) (frame (j+1)) := by
    obtain ⟨p,h0,h1⟩ := remainderSucc (a 6) j hj
    let before := mem j
    let after := Function.update before 6 p
    have h6 : before 6 = p+1 := by simp [before,mem,h0]
    have h5 : after 5 = (0 : M) := by simp [after,before,mem,hz]
    have hdec := sourceDecPositive 3631 3632 6 (some 3633) (by decide) s3631 before tail p h6
    have hjmp := sourceJump 3632 3629 (by decide) s3632 after tail
    have htest := sourceDecZero 3629 3631 5 (some 3630) (by decide) s3629 after tail h5
    have ha : after = mem (j+1) := by simp [after,before,mem,h1]
    change Reaches (frame j) (sourceState 3631 (mem (j+1)) tail)
    rw [←ha]
    exact append (append (oneStep hdec).reaches (oneStep hjmp).reaches) (oneStep htest).reaches
  have h := runMany frame (a 6) (frameDef 3631 (fun i j => mem j i) tail hm) hs (a 6) le_rfl
  have h0 : mem 0 = a := by
    funext i
    by_cases hi : i = 6 <;> simp [mem,hi] <;> exact PRASubtraction.modelSubZero _
  have h1 : mem (a 6) = Function.update a 6 0 := by simp [mem,subSelf]
  change Reaches (sourceState 3631 (mem 0) tail) (sourceState 3631 (mem (a 6)) tail) at h
  rw [h0,h1] at h
  have hd := sourceDecZero 3631 3633 6 (some 3632) (by decide) s3631
    (Function.update a 6 (0 : M)) tail (by simp [regsOfArgs])
  have hj := sourceJump 3633 3660 (by decide) s3633 (Function.update a 6 (0 : M)) tail
  exact appendPositive (append h (oneStep hd).reaches) (oneStep hj)

theorem cleanup (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState 3629 a tail) (sourceState 3660 (values a 0 0) tail) := by
  have hh := drain 3629 3630 3631 5 [] (by decide) s3629 (.jump _ (by decide) s3630) (by decide) a tail
  rw [emptyArgs,subSelf] at hh
  exact appendPositive hh.reaches (drainX (Function.update a 5 (0 : M)) tail (Function.update_self 5 0 a))

#print axioms comparePrefix
#print axioms cleanup
end models
end PA194ModelMPCompare
