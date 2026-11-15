import PA194PAeqEqRelExt
import PA194PAeqAddCongrAtTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.LessCongrTyped
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt
variable {Γ : List Fm}

noncomputable def reflAt (t : Tm) (h : reflexivity ∈ Γ) : ND.Proof Γ (eq t t) := by
  have d : ND.Proof Γ reflexivity := ND.assumption h
  have e := ND.allElim _ t d
  simpa [reflexivity,eq,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e

noncomputable def lessCongrAt (a b c d : Tm)
    (ha : ND.Proof Γ (eq a c)) (hb : ND.Proof Γ (eq b d)) (hl : ND.Proof Γ (less a b))
    (hadd : addCongruence ∈ Γ) (hsym : symmetry ∈ Γ) (htrans : transitivity ∈ Γ) (hrefl : reflexivity ∈ Γ) :
    ND.Proof Γ (less c d) := by
  let P : Semiproposition language 1 := eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)
  have hex : ND.Proof Γ (∃⁰ P) := hl
  apply ND.exsElim hex
  let Δ := P.free :: ND.shifted Γ
  let a' : Tm := Rew.shift a
  let b' : Tm := Rew.shift b
  let c' : Tm := Rew.shift c
  let d' : Tm := Rew.shift d
  let witness : Tm := .fvar 0
  have ha' : ND.Proof Δ (eq a' c') := by
    have h := ND.weaken (ND.shiftProof ha) (Δ := Δ) (by intro q hq; simp [Δ,hq])
    simpa [Δ,a',c',eq,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func] using h
  have hb' : ND.Proof Δ (eq b' d') := by
    have h := ND.weaken (ND.shiftProof hb) (Δ := Δ) (by intro q hq; simp [Δ,hq])
    simpa [Δ,b',d',eq,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func] using h
  have hfreeShift (t : Tm) :
      (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
    simpa [Rew.free] using (Rew.free_bShift_app t)
  have hw : ND.Proof Δ (eq (add a' (succ witness)) b') := by
    have h : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [Δ,P,a',b',witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using h
  have hadd' : addCongruence ∈ Δ := by
    have hh : addCongruence.freeVariables = ∅ := by decide
    change addCongruence ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨addCongruence,hadd,shift_id _ hh⟩
  have hsym' : symmetry ∈ Δ := by
    have hh : symmetry.freeVariables = ∅ := by decide
    change symmetry ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨symmetry,hsym,shift_id _ hh⟩
  have htrans' : transitivity ∈ Δ := by
    have hh : transitivity.freeVariables = ∅ := by decide
    change transitivity ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨transitivity,htrans,shift_id _ hh⟩
  have hrefl' : reflexivity ∈ Δ := by
    have hh : reflexivity.freeVariables = ∅ := by decide
    change reflexivity ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨reflexivity,hrefl,shift_id _ hh⟩
  have hcon : ND.Proof Δ (eq (add a' (succ witness)) (add c' (succ witness))) :=
    addCongrAt a' c' (succ witness) (succ witness) hadd' ha' (reflAt _ hrefl')
  have hrev : ND.Proof Δ (eq (add c' (succ witness)) (add a' (succ witness))) := symmAt _ _ hsym' hcon
  have hres : ND.Proof Δ (eq (add c' (succ witness)) d') :=
    transAt _ _ _ htrans' (transAt _ _ _ htrans' hrev hw) hb'
  let Q : Semiproposition language 1 := eq (add (Rew.bShift c') (succ (.bvar 0))) (Rew.bShift d')
  have hq : ND.Proof Δ (∃⁰ Q) := by
    apply ND.exsIntro Q witness
    simpa [Q,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using hres
  have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := by exact Rew.q_comp_bShift_app Rew.shift t
  simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
  change ND.Proof Δ (Semiformula.rewAux Rew.shift (less c d))
  simpa [Δ,Q,a',b',c',d',P,less,Semiformula.rewAux,
    Rew.shift,Rew.map,Rew.func,Rew.q,eq,add,succ,emptyFn,hshift] using hq
#print axioms lessCongrAt
end PA194PAeq.LessCongrTyped
