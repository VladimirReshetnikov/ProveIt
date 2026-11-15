import PA194PAeqMulOrderLemmas
import PA194PAeqLessShift
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulLtMulTyped
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped PA194PAeq.LessShift
open PA194PAeq.MulRightZero PA194PAeq.MulCongrTyped PA194PAeq.MulOrderLemmas
variable {Γ : List Fm}

noncomputable def atTerms (a b c : Tm) (hab : ND.Proof Γ (less a b)) (hc : ND.Proof Γ (less zero c))
    (hax : ∀ p ∈ MulAssoc.axioms, p ∈ Γ) : ND.Proof Γ (less (mul a c) (mul b c)) := by
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
  have hc' : ND.Proof Δ1 (less zero c') := by
    have h := ND.weaken (ND.shiftProof hc) (Δ := Δ1) (by intro p hp; simp [Δ1,hp])
    simpa [c',shiftLess,zero,Rew.shift,Rew.map,Rew.func,emptyFn] using h
  let Q : Semiproposition language 1 := eq (add (Rew.bShift zero) (succ (.bvar 0))) (Rew.bShift c')
  have hq : ND.Proof Δ1 (∃⁰ Q) := hc'
  have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := by exact Rew.q_comp_bShift_app Rew.shift t
  simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
  have hshiftMul (x y : Tm) : Rew.shift (mul x y) = mul (Rew.shift x) (Rew.shift y) := by simp [mul,Rew.shift,Rew.map,Rew.func]
  rw [shiftLess,hshiftMul,hshiftMul]
  change ND.Proof Δ1 (less (mul a' c') (mul b' c'))
  apply ND.exsElim hq
  let Δ2 := Q.free :: ND.shifted Δ1
  let a'' : Tm := Rew.shift a'
  let b'' : Tm := Rew.shift b'
  let c'' : Tm := Rew.shift c'
  let u' : Tm := Rew.shift u
  let v : Tm := .fvar 0
  have hIn1 (p : Fm) (hm : p ∈ MulAssoc.axioms) : p ∈ Δ1 := by
    change p ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hax p hm,AddOne.shift_id p (MulAssoc.axioms_closed p hm)⟩
  have hIn2 (p : Fm) (hm : p ∈ MulAssoc.axioms) : p ∈ Δ2 := by
    change p ∈ Q.free :: ND.shifted Δ1
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hIn1 p hm,AddOne.shift_id p (MulAssoc.axioms_closed p hm)⟩
  have hu' : ND.Proof Δ2 (eq (add a'' (succ u')) b'') := by
    have h := ND.weaken (ND.shiftProof hu) (Δ := Δ2) (by intro p hp; simp [Δ2,hp])
    simpa [a'',b'',u',eq,add,succ,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func] using h
  have hv : ND.Proof Δ2 (eq (add zero (succ v)) c'') := by
    have h : ND.Proof Δ2 Q.free := ND.assumption (by simp [Δ2])
    simpa [Q,c'',v,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,zero,emptyFn,substShift,hfreeShift] using h
  have hΓ : ∀ p ∈ MulAssoc.axioms, p ∈ Δ2 := fun p hp => hIn2 p hp
  have hcS : ND.Proof Δ2 (eq c'' (succ v)) :=
    transAt _ _ _ (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms]))
      (symmAt _ _ (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) hv)
      (addZeroAt (succ v) (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])))
  let w : Tm := add v (mul u' c'')
  have hpos := positiveFactorAt u' c'' v hcS hΓ
  have h1 := symmAt _ _ (Γ := Δ2) (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms]))
    (addCongrAt (mul a'' c'') (mul a'' c'') (mul (succ u') c'') (succ w)
      (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms]))
      (reflAt _ (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms]))) hpos)
  have h2 := symmAt _ _ (Γ := Δ2) (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms]))
    (rightDistrAt a'' (succ u') c'' hΓ)
  have h3 := mulCongrAt (add a'' (succ u')) b'' c'' c'' (Γ := Δ2)
    (hIn2 _ (by simp [MulAssoc.axioms])) hu' (reflAt _ (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])))
  have he : ND.Proof Δ2 (eq (add (mul a'' c'') (succ w)) (mul b'' c'')) :=
    transAt _ _ _ (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) h1
      (transAt _ _ _ (hIn2 _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) h2 h3)
  let R : Semiproposition language 1 := eq (add (Rew.bShift (mul a'' c'')) (succ (.bvar 0))) (Rew.bShift (mul b'' c''))
  have hr : ND.Proof Δ2 (∃⁰ R) := by
    apply ND.exsIntro R w
    simpa [R,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using he
  rw [shiftLess,hshiftMul,hshiftMul]
  change ND.Proof Δ2 (less (mul a'' c'') (mul b'' c''))
  exact hr
#print axioms atTerms
end PA194PAeq.MulLtMulTyped
