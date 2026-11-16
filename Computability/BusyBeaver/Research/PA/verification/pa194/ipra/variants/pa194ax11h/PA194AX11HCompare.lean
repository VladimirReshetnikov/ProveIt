import PA194AX11HCandidateDrain
import PA194AX11HCompareRows
import PA194ModelMPCompare
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194AX11HCompare
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194AX11HCompareRows
open PA194ModelMPCompare (values rest remainderSucc restDef emptyArgs)
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

abbrev Reaches (s t : M) : Prop := PA194PausedReach.Reaches PA194AX11HSource.step s t

theorem append {s t u : M} (h : Reaches s t) (h' : Reaches t u) : Reaches s u :=
  PA194PausedReach.append _ h h'

theorem oneStep {s t : M} (h : F PA194AX11HSource.step ![s] = t) : Reaches s t :=
  PA194PausedReach.oneStep _ h

theorem comparePrefix (a : Fin 11 → M) (tail k : M) (hh : k ≤ a 5) (hx : k ≤ a 6) :
    Reaches (sourceState 3642 a tail) (sourceState 3642 (rest a k) tail) := by
  let frame := fun j => sourceState 3642 (rest a j) tail
  have hstep (j : M) (hj : j < k) : Reaches (frame j) (frame (j+1)) := by
    obtain ⟨h,h0,h1⟩ := remainderSucc (a 5) j (lt_of_lt_of_le hj hh)
    obtain ⟨x,x0,x1⟩ := remainderSucc (a 6) j (lt_of_lt_of_le hj hx)
    let curr := rest a j
    let an := Function.update curr 5 h
    let bn := Function.update an 6 x
    have hcurr : curr 5 = h+1 := by simp [curr,rest,values,h0]
    have xcurr : an 6 = x+1 := by simp [an,curr,rest,values,x0]
    have hs := PA194AX11HSourceAt.sourceDecPositive 3642 3643 5 (some 3646) (by decide) s3642 curr tail h hcurr
    have ht := PA194AX11HSourceAt.sourceDecPositive 3643 3644 6 (some 3645) (by decide) s3643 an tail x xcurr
    have hu := PA194AX11HSourceAt.sourceJump 3644 3642 (by decide) s3644 bn tail
    have hb : bn = rest a (j+1) := by
      funext i
      fin_cases i <;> simp [bn,an,curr,rest,values,h1,x1]
    change Reaches (frame j) (sourceState 3642 (rest a (j+1)) tail)
    rw [←hb]
    exact append (append (oneStep hs) (oneStep ht)) (oneStep hu)
  have h := PA194PausedReach.runMany PA194AX11HSource.step frame k (frameDef 3642 (fun i j => rest a j i) tail (restDef a)) hstep k le_rfl
  have hz : rest a 0 = a := by
    funext i
    fin_cases i <;> simp [rest,values] <;> exact PRASubtraction.modelSubZero _
  change Reaches (sourceState 3642 (rest a 0) tail) (sourceState 3642 (rest a k) tail) at h
  rwa [hz] at h


theorem drainX (a : Fin 11 → M) (tail : M) (hz : a 5 = 0) :
    Reaches (sourceState 3649 a tail) (sourceState 3659 (Function.update a 6 0) tail) := by
  let mem := fun j => Function.update a 6 (F subCode ![a 6,j])
  let frame := fun j => sourceState 3649 (mem j) tail
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
    have hdec := PA194AX11HSourceAt.sourceDecPositive 3649 3650 6 (some 3651) (by decide) s3649 before tail p h6
    have hjmp := PA194AX11HSourceAt.sourceJump 3650 3647 (by decide) s3650 after tail
    have htest := PA194AX11HSourceAt.sourceDecZero 3647 3649 5 (some 3648) (by decide) s3647 after tail h5
    have ha : after = mem (j+1) := by simp [after,before,mem,h1]
    change Reaches (frame j) (sourceState 3649 (mem (j+1)) tail)
    rw [←ha]
    exact append (append (oneStep hdec) (oneStep hjmp)) (oneStep htest)
  have h := PA194PausedReach.runMany PA194AX11HSource.step frame (a 6) (frameDef 3649 (fun i j => mem j i) tail hm) hs (a 6) le_rfl
  have h0 : mem 0 = a := by
    funext i
    by_cases hi : i = 6 <;> simp [mem,hi] <;> exact PRASubtraction.modelSubZero _
  have h1 : mem (a 6) = Function.update a 6 0 := by simp [mem,subSelf]
  change Reaches (sourceState 3649 (mem 0) tail) (sourceState 3649 (mem (a 6)) tail) at h
  rw [h0,h1] at h
  have hd := PA194AX11HSourceAt.sourceDecZero 3649 3651 6 (some 3650) (by decide) s3649
    (Function.update a 6 (0 : M)) tail (by simp [regsOfArgs])
  have hj := PA194AX11HSourceAt.sourceJump 3651 3659 (by decide) s3651 (Function.update a 6 (0 : M)) tail
  exact append (append h (oneStep hd)) (oneStep hj)

theorem cleanup (a : Fin 11 → M) (tail : M) :
    Reaches (sourceState 3647 a tail) (sourceState 3659 (values a 0 0) tail) := by
  have hh := PA194AX11HCandidateDrain.drain 3647 3648 3649 5 [] (by decide) s3647 (.jump _ (by decide) s3648) (by decide) a tail
  rw [emptyArgs,subSelf] at hh
  exact append hh (drainX (Function.update a 5 (0 : M)) tail (Function.update_self 5 0 a))


theorem compareEqual (a : Fin 11 → M) (tail : M) (h : a 5 = a 6) :
    Reaches (sourceState 3642 a tail) (sourceState 3652 (values a 0 0) tail) := by
  have hc := comparePrefix a tail (a 5) le_rfl (le_of_eq h)
  have he : rest a (a 5) = values a 0 0 := by unfold rest; rw [h,subSelf]
  rw [he] at hc
  let b := values a 0 0
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = 0 := by simp [b,values,regsOfArgs]
  have h1 := PA194AX11HSourceAt.sourceDecZero 3642 3646 5 (some 3643) (by decide) s3642 b tail h5
  have h2 := PA194AX11HSourceAt.sourceDecZero 3646 3652 6 (some 3647) (by decide) s3646 b tail h6
  exact append (append hc (oneStep h1)) (oneStep h2)

theorem compareLess (a : Fin 11 → M) (tail : M) (h : a 5 < a 6) :
    Reaches (sourceState 3642 a tail) (sourceState 3659 (values a 0 0) tail) := by
  have hc := comparePrefix a tail (a 5) le_rfl (le_of_lt h)
  obtain ⟨x,hx,_⟩ := remainderSucc (a 6) (a 5) h
  let b := values a 0 (x+1)
  let c := Function.update b 6 x
  have he : rest a (a 5) = b := by unfold rest b; rw [subSelf,hx]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = x+1 := by simp [b,values,regsOfArgs]
  have h1 := PA194AX11HSourceAt.sourceDecZero 3642 3646 5 (some 3643) (by decide) s3642 b tail h5
  have h2 := PA194AX11HSourceAt.sourceDecPositive 3646 3647 6 (some 3652) (by decide) s3646 b tail x h6
  have h3 := cleanup c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i; fin_cases i <;> simp [c,b,values]
  rw [hend] at h3
  exact append (append (append hc (oneStep h1)) (oneStep h2)) h3

theorem compareGreater (a : Fin 11 → M) (tail : M) (h : a 6 < a 5) :
    Reaches (sourceState 3642 a tail) (sourceState 3659 (values a 0 0) tail) := by
  have hc := comparePrefix a tail (a 6) (le_of_lt h) le_rfl
  obtain ⟨v,hv,_⟩ := remainderSucc (a 5) (a 6) h
  let b := values a (v+1) 0
  let c := Function.update b 5 v
  have he : rest a (a 6) = b := by unfold rest b; rw [subSelf,hv]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = v+1 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs c 6 = 0 := by simp [c,b,values,regsOfArgs]
  have h1 := PA194AX11HSourceAt.sourceDecPositive 3642 3643 5 (some 3646) (by decide) s3642 b tail v h5
  have h2 := PA194AX11HSourceAt.sourceDecZero 3643 3645 6 (some 3644) (by decide) s3643 c tail h6
  have h3 := PA194AX11HSourceAt.sourceJump 3645 3647 (by decide) s3645 c tail
  have h4 := cleanup c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i; fin_cases i <;> simp [c,b,values]
  rw [hend] at h4
  exact append (append (append (append hc (oneStep h1)) (oneStep h2))
    (oneStep h3)) h4

theorem compare (a : Fin 11 → M) (tail : M) :
    Reaches (sourceState 3642 a tail)
      (sourceState (if a 5 = a 6 then 3652 else 3659) (values a 0 0) tail) := by
  rcases lt_trichotomy (a 5) (a 6) with h | h | h
  · rw [if_neg (ne_of_lt h)]
    exact compareLess a tail h
  · rw [if_pos h]
    exact compareEqual a tail h
  · rw [if_neg (ne_of_gt h)]
    exact compareGreater a tail h

#print axioms comparePrefix
#print axioms cleanup
#print axioms compare
end models
end PA194AX11HCompare
