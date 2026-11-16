import PA194ProgramDrain
import PA194ModelMPCompare

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ProgramCompare
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ProgramDrain
open PA194ModelMPDrain (argsAfter location tally subSelf partialDef frameDef subByDef)

structure Rows (program : Program) (base : Nat) (fail : Nat) : Prop where
  valid : base+9 < program.length
  htest : row program base = some (.dec 5 (some (base+4)) (some (base+1)))
  xtest : row program (base+1) = some (.dec 6 (some (base+3)) (some (base+2)))
  backLoop : row program (base+2) = some (.jump (some base))
  toClean : row program (base+3) = some (.jump (some (base+5)))
  equalTest : row program (base+4) = some (.dec 6 (some (base+10)) (some (base+5)))
  cleanH : row program (base+5) = some (.dec 5 (some (base+7)) (some (base+6)))
  backH : row program (base+6) = some (.jump (some (base+5)))
  cleanX : row program (base+7) = some (.dec 6 (some (base+9)) (some (base+8)))
  backX : row program (base+8) = some (.jump (some (base+5)))
  toFail : row program (base+9) = some (.jump (some fail))

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

theorem comparePrefix (program : Program) (base fail : Nat) (rows : Rows program base fail) (a : Fin 11 → M) (tail k : M) (hh : k ≤ a 5) (hx : k ≤ a 6) :
    Reaches program (sourceState (base+0) a tail) (sourceState (base+0) (rest a k) tail) := by
  let frame := fun j => sourceState (base+0) (rest a j) tail
  have hstep (j : M) (hj : j < k) : Reaches program (frame j) (frame (j+1)) := by
    obtain ⟨h,h0,h1⟩ := remainderSucc (a 5) j (lt_of_lt_of_le hj hh)
    obtain ⟨x,x0,x1⟩ := remainderSucc (a 6) j (lt_of_lt_of_le hj hx)
    let curr := rest a j
    let an := Function.update curr 5 h
    let bn := Function.update an 6 x
    have hcurr : curr 5 = h+1 := by simp [curr,rest,values,h0]
    have xcurr : an 6 = x+1 := by simp [an,curr,rest,values,x0]
    have hs := sourceDecPositive program (base+0) (base+1) 5 (some (base+4)) (by have := rows.valid; omega) rows.htest curr tail h hcurr
    have ht := sourceDecPositive program (base+1) (base+2) 6 (some (base+3)) (by have := rows.valid; omega) rows.xtest an tail x xcurr
    have hu := sourceJump program (base+2) (base+0) (by have := rows.valid; omega) rows.backLoop bn tail
    have hb : bn = rest a (j+1) := by
      funext i
      fin_cases i <;> simp [bn,an,curr,rest,values,h1,x1]
    change Reaches program (frame j) (sourceState (base+0) (rest a (j+1)) tail)
    rw [←hb]
    exact append program (append program (oneStep program hs).reaches (oneStep program ht).reaches) (oneStep program hu).reaches
  have h := runMany program frame k (frameDef (base+0) (fun i j => rest a j i) tail (restDef a)) hstep k le_rfl
  have hz : rest a 0 = a := by
    funext i
    fin_cases i <;> simp [rest,values] <;> exact PRASubtraction.modelSubZero _
  change Reaches program (sourceState (base+0) (rest a 0) tail) (sourceState (base+0) (rest a k) tail) at h
  rwa [hz] at h

theorem emptyArgs (a : Fin 11 → M) (r : Fin 9) (j : M) :
    argsAfter a r [] j = Function.update a (location r) (F subCode ![a (location r),j]) := by
  funext i
  by_cases h : i = location r
  · simp [argsAfter,h]
  · simp [argsAfter,h,tally,show modelNumeral M 0 = (0:M) from rfl]

theorem drainX (program : Program) (base fail : Nat) (rows : Rows program base fail) (a : Fin 11 → M) (tail : M) (hz : a 5 = 0) :
    ReachesPositive program (sourceState (base+7) a tail) (sourceState fail (Function.update a 6 0) tail) := by
  let mem := fun j => Function.update a 6 (F subCode ![a 6,j])
  let frame := fun j => sourceState (base+7) (mem j) tail
  have hm (i : Fin 11) : 𝚺₁-Function₁ (fun j => mem j i) := by
    have he : (fun j : M => mem j i) = fun j => argsAfter a 6 [] j i := by
      funext j
      rw [emptyArgs]
      rfl
    rw [he]
    exact partialDef a 6 [] i
  have hs (j : M) (hj : j < a 6) : Reaches program (frame j) (frame (j+1)) := by
    obtain ⟨p,h0,h1⟩ := remainderSucc (a 6) j hj
    let before := mem j
    let after := Function.update before 6 p
    have h6 : before 6 = p+1 := by simp [before,mem,h0]
    have h5 : after 5 = (0 : M) := by simp [after,before,mem,hz]
    have hdec := sourceDecPositive program (base+7) (base+8) 6 (some (base+9)) (by have := rows.valid; omega) rows.cleanX before tail p h6
    have hjmp := sourceJump program (base+8) (base+5) (by have := rows.valid; omega) rows.backX after tail
    have htest := sourceDecZero program (base+5) (base+7) 5 (some (base+6)) (by have := rows.valid; omega) rows.cleanH after tail h5
    have ha : after = mem (j+1) := by simp [after,before,mem,h1]
    change Reaches program (frame j) (sourceState (base+7) (mem (j+1)) tail)
    rw [←ha]
    exact append program (append program (oneStep program hdec).reaches (oneStep program hjmp).reaches) (oneStep program htest).reaches
  have h := runMany program frame (a 6) (frameDef (base+7) (fun i j => mem j i) tail hm) hs (a 6) le_rfl
  have h0 : mem 0 = a := by
    funext i
    by_cases hi : i = 6 <;> simp [mem,hi] <;> exact PRASubtraction.modelSubZero _
  have h1 : mem (a 6) = Function.update a 6 0 := by simp [mem,subSelf]
  change Reaches program (sourceState (base+7) (mem 0) tail) (sourceState (base+7) (mem (a 6)) tail) at h
  rw [h0,h1] at h
  have hd := sourceDecZero program (base+7) (base+9) 6 (some (base+8)) (by have := rows.valid; omega) rows.cleanX
    (Function.update a 6 (0 : M)) tail (by simp [regsOfArgs])
  have hj := sourceJump program (base+9) fail (by have := rows.valid; omega) rows.toFail (Function.update a 6 (0 : M)) tail
  exact appendPositive program (append program h (oneStep program hd).reaches) (oneStep program hj)

theorem cleanup (program : Program) (base fail : Nat) (rows : Rows program base fail) (a : Fin 11 → M) (tail : M) :
    ReachesPositive program (sourceState (base+5) a tail) (sourceState fail (values a 0 0) tail) := by
  have hh := drain program (base+5) (base+6) (base+7) 5 [] (by have := rows.valid; omega) rows.cleanH (.jump _ (by have := rows.valid; omega) rows.backH) (by decide) a tail
  rw [emptyArgs,subSelf] at hh
  exact appendPositive program hh.reaches (drainX program base fail rows (Function.update a 5 (0 : M)) tail (Function.update_self 5 0 a))

#print axioms comparePrefix
#print axioms cleanup
end models
end PA194ProgramCompare
