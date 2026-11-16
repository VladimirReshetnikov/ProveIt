import PA194ModelMPCompare

/-! The 12-site destructive H/X comparison clears T exactly on equality. -/

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ModelAXCompare
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194ModelMPCompare

structure CompareRows (base : Nat) : Prop where
  valid : base+11 < 3673
  compareH : row base = some (.dec 5 (some (base+4)) (some (base+1)))
  compareX : row (base+1) = some (.dec 6 (some (base+3)) (some (base+2)))
  repeatCompare : row (base+2) = some (.jump (some base))
  fewerX : row (base+3) = some (.jump (some (base+5)))
  equalOrFewerH : row (base+4) = some (.dec 6 (some (base+10)) (some (base+5)))
  scrubH : row (base+5) = some (.dec 5 (some (base+7)) (some (base+6)))
  repeatScrubH : row (base+6) = some (.jump (some (base+5)))
  scrubX : row (base+7) = some (.dec 6 (some (base+9)) (some (base+8)))
  repeatScrubX : row (base+8) = some (.jump (some (base+5)))
  done : row (base+9) = some (.jump (some (base+12)))
  scrubT : row (base+10) = some (.dec 1 (some (base+12)) (some (base+11)))
  repeatScrubT : row (base+11) = some (.jump (some (base+10)))

private theorem CompareRows.bound {base : Nat} (r : CompareRows base) (i : Nat) (hi : i ≤ 11) :
    base+i < 3673 := by have := r.valid; omega

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

theorem comparePrefix (base : Nat) (r : CompareRows base)
    (a : Fin 11 → M) (tail k : M) (hh : k ≤ a 5) (hx : k ≤ a 6) :
    Reaches (sourceState base a tail) (sourceState base (rest a k) tail) := by
  let frame := fun j => sourceState base (rest a j) tail
  have hstep (j : M) (hj : j < k) : Reaches (frame j) (frame (j+1)) := by
    obtain ⟨h,h0,h1⟩ := remainderSucc (a 5) j (lt_of_lt_of_le hj hh)
    obtain ⟨x,x0,x1⟩ := remainderSucc (a 6) j (lt_of_lt_of_le hj hx)
    let curr := rest a j
    let an := Function.update curr 5 h
    let bn := Function.update an 6 x
    have hcurr : curr 5 = h+1 := by simp [curr,rest,values,h0]
    have xcurr : an 6 = x+1 := by simp [an,curr,rest,values,x0]
    have hs := sourceDecPositive base (base+1) 5 (some (base+4)) (r.bound 0 (by decide))
      r.compareH curr tail h hcurr
    have ht := sourceDecPositive (base+1) (base+2) 6 (some (base+3)) (r.bound 1 (by decide))
      r.compareX an tail x xcurr
    have hu := sourceJump (base+2) base (r.bound 2 (by decide)) r.repeatCompare bn tail
    have hb : bn = rest a (j+1) := by
      funext i
      fin_cases i <;> simp [bn,an,curr,rest,values,h1,x1]
    change Reaches (frame j) (sourceState base (rest a (j+1)) tail)
    rw [←hb]
    exact append (append (oneStep hs).reaches (oneStep ht).reaches) (oneStep hu).reaches
  have h := runMany frame k (frameDef base (fun i j => rest a j i) tail (restDef a)) hstep k le_rfl
  have hz : rest a 0 = a := by
    funext i
    fin_cases i <;> simp [rest,values] <;> exact PRASubtraction.modelSubZero _
  change Reaches (sourceState base (rest a 0) tail) (sourceState base (rest a k) tail) at h
  rwa [hz] at h

private theorem scrubX (base : Nat) (r : CompareRows base) (a : Fin 11 → M) (tail : M) (hz : a 5 = 0) :
    ReachesPositive (sourceState (base+7) a tail)
      (sourceState (base+12) (Function.update a 6 0) tail) := by
  let mem := fun j => Function.update a 6 (F subCode ![a 6,j])
  let frame := fun j => sourceState (base+7) (mem j) tail
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
    have hdec := sourceDecPositive (base+7) (base+8) 6 (some (base+9)) (r.bound 7 (by decide))
      r.scrubX before tail p h6
    have hjmp := sourceJump (base+8) (base+5) (r.bound 8 (by decide)) r.repeatScrubX after tail
    have htest := sourceDecZero (base+5) (base+7) 5 (some (base+6)) (r.bound 5 (by decide))
      r.scrubH after tail h5
    have ha : after = mem (j+1) := by simp [after,before,mem,h1]
    change Reaches (frame j) (sourceState (base+7) (mem (j+1)) tail)
    rw [←ha]
    exact append (append (oneStep hdec).reaches (oneStep hjmp).reaches) (oneStep htest).reaches
  have h := runMany frame (a 6) (frameDef (base+7) (fun i j => mem j i) tail hm) hs (a 6) le_rfl
  have h0 : mem 0 = a := by
    funext i
    by_cases hi : i = 6 <;> simp [mem,hi] <;> exact PRASubtraction.modelSubZero _
  have h1 : mem (a 6) = Function.update a 6 0 := by simp [mem,subSelf]
  change Reaches (sourceState (base+7) (mem 0) tail) (sourceState (base+7) (mem (a 6)) tail) at h
  rw [h0,h1] at h
  have hd := sourceDecZero (base+7) (base+9) 6 (some (base+8)) (r.bound 7 (by decide)) r.scrubX
    (Function.update a 6 (0 : M)) tail (by simp [regsOfArgs])
  have hj := sourceJump (base+9) (base+12) (r.bound 9 (by decide)) r.done (Function.update a 6 (0 : M)) tail
  exact appendPositive (append h (oneStep hd).reaches) (oneStep hj)

private theorem cleanup (base : Nat) (r : CompareRows base) (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState (base+5) a tail) (sourceState (base+12) (values a 0 0) tail) := by
  have hh := drain (base+5) (base+6) (base+7) 5 [] (r.bound 5 (by decide)) r.scrubH
    (.jump _ (r.bound 6 (by decide)) r.repeatScrubH) (by decide) a tail
  rw [emptyArgs,subSelf] at hh
  exact appendPositive hh.reaches (scrubX base r (Function.update a 5 (0 : M)) tail (Function.update_self 5 0 a))

noncomputable def output (a : Fin 11 → M) : Fin 11 → M := by
  classical
  exact values (Function.update a 1 (if a 5 = a 6 then 0 else a 1)) 0 0

private theorem compareEqual (base : Nat) (r : CompareRows base) (a : Fin 11 → M) (tail : M)
    (h : a 5 = a 6) :
    ReachesPositive (sourceState base a tail) (sourceState (base+12) (output a) tail) := by
  have hc := comparePrefix base r a tail (a 5) le_rfl (le_of_eq h)
  have he : rest a (a 5) = values a 0 0 := by unfold rest; rw [h,subSelf]
  rw [he] at hc
  let b := values a 0 0
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = 0 := by simp [b,values,regsOfArgs]
  have h1 := sourceDecZero base (base+4) 5 (some (base+1)) (r.bound 0 (by decide)) r.compareH b tail h5
  have h2 := sourceDecZero (base+4) (base+10) 6 (some (base+5)) (r.bound 4 (by decide))
    r.equalOrFewerH b tail h6
  have h3 := drain (base+10) (base+11) (base+12) 1 [] (r.bound 10 (by decide)) r.scrubT
    (.jump _ (r.bound 11 (by decide)) r.repeatScrubT) (by decide) b tail
  have hout : argsAfter b 1 [] (b (location 1)) = output a := by
    rw [emptyArgs,subSelf]
    funext i
    fin_cases i <;> simp [b,values,output,h,location]
  rw [hout] at h3
  exact appendPositive (append (append hc (oneStep h1).reaches) (oneStep h2).reaches) h3

private theorem output_ne (a : Fin 11 → M) (h : a 5 ≠ a 6) : output a = values a 0 0 := by
  simp [output,h,Function.update_eq_self]

private theorem compareLess (base : Nat) (r : CompareRows base) (a : Fin 11 → M) (tail : M)
    (h : a 5 < a 6) :
    ReachesPositive (sourceState base a tail) (sourceState (base+12) (output a) tail) := by
  rw [output_ne a (ne_of_lt h)]
  have hc := comparePrefix base r a tail (a 5) le_rfl (le_of_lt h)
  obtain ⟨x,hx,_⟩ := remainderSucc (a 6) (a 5) h
  let b := values a 0 (x+1)
  let c := Function.update b 6 x
  have he : rest a (a 5) = b := by unfold rest b; rw [subSelf,hx]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = 0 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs b 6 = x+1 := by simp [b,values,regsOfArgs]
  have h1 := sourceDecZero base (base+4) 5 (some (base+1)) (r.bound 0 (by decide)) r.compareH b tail h5
  have h2 := sourceDecPositive (base+4) (base+5) 6 (some (base+10)) (r.bound 4 (by decide))
    r.equalOrFewerH b tail x h6
  have h3 := cleanup base r c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i
    fin_cases i <;> simp [c,b,values]
  rw [hend] at h3
  exact appendPositive (append (append hc (oneStep h1).reaches) (oneStep h2).reaches) h3

private theorem compareGreater (base : Nat) (r : CompareRows base) (a : Fin 11 → M) (tail : M)
    (h : a 6 < a 5) :
    ReachesPositive (sourceState base a tail) (sourceState (base+12) (output a) tail) := by
  rw [output_ne a (ne_of_gt h)]
  have hc := comparePrefix base r a tail (a 6) (le_of_lt h) le_rfl
  obtain ⟨v,hv,_⟩ := remainderSucc (a 5) (a 6) h
  let b := values a (v+1) 0
  let c := Function.update b 5 v
  have he : rest a (a 6) = b := by unfold rest b; rw [subSelf,hv]
  rw [he] at hc
  have h5 : regsOfArgs b 5 = v+1 := by simp [b,values,regsOfArgs]
  have h6 : regsOfArgs c 6 = 0 := by simp [c,b,values,regsOfArgs]
  have h1 := sourceDecPositive base (base+1) 5 (some (base+4)) (r.bound 0 (by decide))
    r.compareH b tail v h5
  have h2 := sourceDecZero (base+1) (base+3) 6 (some (base+2)) (r.bound 1 (by decide))
    r.compareX c tail h6
  have h3 := sourceJump (base+3) (base+5) (r.bound 3 (by decide)) r.fewerX c tail
  have h4 := cleanup base r c tail
  have hend : values c 0 0 = values a 0 0 := by
    funext i
    fin_cases i <;> simp [c,b,values]
  rw [hend] at h4
  exact appendPositive (append (append (append hc (oneStep h1).reaches) (oneStep h2).reaches)
    (oneStep h3).reaches) h4

theorem compare (base : Nat) (r : CompareRows base) (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState base a tail) (sourceState (base+12) (output a) tail) := by
  rcases lt_trichotomy (a 5) (a 6) with h | h | h
  · exact compareLess base r a tail h
  · exact compareEqual base r a tail h
  · exact compareGreater base r a tail h

#print axioms compare
end models
end PA194ModelAXCompare
