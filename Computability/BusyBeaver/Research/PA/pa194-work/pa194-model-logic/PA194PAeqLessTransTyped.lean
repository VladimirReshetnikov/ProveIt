import PA194PAeqLessShift
import PA194PAeqAddLawsAt
import PA194PAeqAddLtAdd
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.LessTransTyped
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped PA194PAeq.AddLawsAt PA194PAeq.LessShift
variable {Γ : List Fm}

noncomputable def lessTransAt (a b c : Tm)
    (hab : ND.Proof Γ (less a b)) (hbc : ND.Proof Γ (less b c))
    (hax : ∀ p ∈ AddLtAdd.axioms, p ∈ Γ) : ND.Proof Γ (less a c) := by
  let P : Semiproposition language 1 := eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)
  have hp : ND.Proof Γ (∃⁰ P) := hab
  apply ND.exsElim hp
  let Δ1 := P.free :: ND.shifted Γ
  let a' : Tm := Rew.shift a
  let b' : Tm := Rew.shift b
  let c' : Tm := Rew.shift c
  let u : Tm := .fvar 0
  have hfreeShift (t : Tm) :
      (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
    simpa [Rew.free] using (Rew.free_bShift_app t)
  have hu : ND.Proof Δ1 (eq (add a' (succ u)) b') := by
    have h : ND.Proof Δ1 P.free := ND.assumption (by simp [Δ1])
    simpa [P,a',b',u,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using h
  have hbc' : ND.Proof Δ1 (less b' c') := by
    have h := ND.weaken (ND.shiftProof hbc) (Δ := Δ1) (by intro p hp; simp [Δ1,hp])
    simpa [b',c',shiftLess] using h
  let Q : Semiproposition language 1 := eq (add (Rew.bShift b') (succ (.bvar 0))) (Rew.bShift c')
  have hq : ND.Proof Δ1 (∃⁰ Q) := hbc'
  rw [shiftLess]
  change ND.Proof Δ1 (less a' c')
  apply ND.exsElim hq
  let Δ2 := Q.free :: ND.shifted Δ1
  let a'' : Tm := Rew.shift a'
  let b'' : Tm := Rew.shift b'
  let c'' : Tm := Rew.shift c'
  let u' : Tm := Rew.shift u
  let v : Tm := .fvar 0
  have hIn1 (p : Fm) (hm : p ∈ AddLtAdd.axioms) : p ∈ Δ1 := by
    change p ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hax p hm,shift_id p (AddLtAdd.axioms_closed p hm)⟩
  have hIn2 (p : Fm) (hm : p ∈ AddLtAdd.axioms) : p ∈ Δ2 := by
    change p ∈ Q.free :: ND.shifted Δ1
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hIn1 p hm,shift_id p (AddLtAdd.axioms_closed p hm)⟩
  have hu' : ND.Proof Δ2 (eq (add a'' (succ u')) b'') := by
    have h := ND.weaken (ND.shiftProof hu) (Δ := Δ2) (by intro p hp; simp [Δ2,hp])
    simpa [a'',b'',u',eq,add,succ,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func] using h
  have hv : ND.Proof Δ2 (eq (add b'' (succ v)) c'') := by
    have h : ND.Proof Δ2 Q.free := ND.assumption (by simp [Δ2])
    simpa [Q,b'',c'',v,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using h
  have hAssoc : ∀ p ∈ AddAssoc.axioms, p ∈ Δ2 := fun p hp => hIn2 p (AddLtAdd.subset_assoc p hp)
  let w : Tm := add u' (succ v)
  have hA := symmAt _ _ (Γ := Δ2) (hIn2 _ (by simp [AddLtAdd.axioms]))
    (addSuccAt u' (succ v) (hIn2 _ (by simp [AddLtAdd.axioms])))
  have h1 : ND.Proof Δ2 (eq (add a'' (succ w)) (add a'' (add (succ u') (succ v)))) :=
    addCongrAt _ _ _ _ (hIn2 _ (by simp [AddLtAdd.axioms])) (reflAt _ (hIn2 _ (by simp [AddLtAdd.axioms]))) hA
  have h2 := symmAt _ _ (Γ := Δ2) (hIn2 _ (by simp [AddLtAdd.axioms])) (assocAt a'' (succ u') (succ v) hAssoc)
  have h3 := addCongrAt (add a'' (succ u')) b'' (succ v) (succ v) (Γ := Δ2)
    (hIn2 _ (by simp [AddLtAdd.axioms])) hu' (reflAt _ (hIn2 _ (by simp [AddLtAdd.axioms])))
  have he : ND.Proof Δ2 (eq (add a'' (succ w)) c'') :=
    transAt _ _ _ (hIn2 _ (by simp [AddLtAdd.axioms])) h1
      (transAt _ _ _ (hIn2 _ (by simp [AddLtAdd.axioms])) h2
        (transAt _ _ _ (hIn2 _ (by simp [AddLtAdd.axioms])) h3 hv))
  let R : Semiproposition language 1 := eq (add (Rew.bShift a'') (succ (.bvar 0))) (Rew.bShift c'')
  have hr : ND.Proof Δ2 (∃⁰ R) := by
    apply ND.exsIntro R w
    simpa [R,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using he
  change ND.Proof Δ2 ((less a' c').shift)
  rw [shiftLess]
  exact hr
#print axioms lessTransAt
end PA194PAeq.LessTransTyped
