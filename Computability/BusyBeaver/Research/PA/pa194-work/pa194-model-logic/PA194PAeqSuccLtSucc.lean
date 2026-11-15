import PA194PAeqLessShift
import PA194PAeqAddLtAdd
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.SuccLtSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.LessShift
variable {Γ : List Fm}
noncomputable def atTerms (a b : Tm) (h : ND.Proof Γ (less a b))
    (hax : ∀ p ∈ AddLtAdd.axioms, p ∈ Γ) : ND.Proof Γ (less (succ a) (succ b)) := by
  let P : Semiproposition language 1 := eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)
  have hp : ND.Proof Γ (∃⁰ P) := h
  apply ND.exsElim hp
  let Δ := P.free :: ND.shifted Γ
  let a' : Tm := Rew.shift a
  let b' : Tm := Rew.shift b
  let witness : Tm := .fvar 0
  have hIn (p : Fm) (hm : p ∈ AddLtAdd.axioms) : p ∈ Δ := by
    change p ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hax p hm,shift_id p (AddLtAdd.axioms_closed p hm)⟩
  have hfreeShift (t : Tm) :
      (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
    simpa [Rew.free] using (Rew.free_bShift_app t)
  have hw : ND.Proof Δ (eq (add a' (succ witness)) b') := by
    have hp' : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [P,a',b',witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using hp'
  have h1 := addSuccAt a' (succ witness) (Γ := Δ) (hIn _ (by simp [AddLtAdd.axioms]))
  have h2 := succCongrAt _ _ (Γ := Δ) (hIn _ (by simp [AddLtAdd.axioms])) hw
  have he : ND.Proof Δ (eq (add (succ a') (succ witness)) (succ b')) :=
    transAt _ _ _ (hIn _ (by simp [AddLtAdd.axioms])) h1 h2
  let Q : Semiproposition language 1 := eq (add (Rew.bShift (succ a')) (succ (.bvar 0))) (Rew.bShift (succ b'))
  have hq : ND.Proof Δ (∃⁰ Q) := by
    apply ND.exsIntro Q witness
    simpa [Q,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using he
  have hshiftSucc (t : Tm) : Rew.shift (succ t) = succ (Rew.shift t) := by simp [succ,Rew.shift,Rew.map,Rew.func]
  rw [shiftLess,hshiftSucc,hshiftSucc]
  exact hq
#print axioms atTerms
end PA194PAeq.SuccLtSucc
