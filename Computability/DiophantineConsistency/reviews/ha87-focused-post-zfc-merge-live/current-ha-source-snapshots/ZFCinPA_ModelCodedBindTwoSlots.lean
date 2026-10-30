import ZFCinPA.ModelCodedBindOne

set_option autoImplicit false

/-!
Generalized two-slot reindexing of internal syntax. All depths, selected labels,
target indices and syntax codes are internal. The represented vector fixes
old slots and sends the two newly bound slots to arbitrary target bound slots.
The intended Collection client needs only target pairs (1,0), (2,0), (0,1).
The scope is syntax identities; decoded G provability is a separate client.
-/
namespace LeanProofs.ZFCinPA.ModelCodedBindTwoSlots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def twoSlotVec (L : Language) [L.Encodable] [L.LORDefinable]
    (depth i j : V) : V := qVecIter L depth (^#i ∷ ^#j ∷ 0)
noncomputable def twoSlotVecDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 := .mkSigma “out depth i j.
      ∃ bi, !qqBvarDef bi i ∧ ∃ bj, !qqBvarDef bj j ∧
      ∃ vj, !adjoinDef vj bj 0 ∧ ∃ v, !adjoinDef v bi vj ∧
      !(qVecIterDef L) out depth v”
instance twoSlotVec_defined :
    𝚺₁-Function₃[V] (twoSlotVec L) via twoSlotVecDef L :=
  .mk fun e => by simp [twoSlotVecDef,twoSlotVec]
private instance twoSlotVec_delta : 𝚫₁-Function₃[V] (twoSlotVec L) :=
  twoSlotVec_defined.graph_delta.to_definable
private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance termBindOneVecAt_delta : 𝚫₁-Function₄[V] (termBindOneVecAt L) :=
  termBindOneVecAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

private lemma bindOne_offset_isUFormula {depth p : V} (hp : IsSemiformula L depth p)
    (chosen offset : V) : IsUFormula L (bindOneAt L chosen (depth+offset) p) := by
  have hp' : IsSemiformula L (depth+offset) p :=
    ⟨hp.isUFormula,le_trans hp.bv_le (by simp)⟩
  exact (bindOneAt_isSemiformula hp' chosen).isUFormula

@[simp] lemma twoSlotVec_zero (i j : V) : twoSlotVec (V := V) L 0 i j = ^#i ∷ ^#j ∷ 0 := by
  simp [twoSlotVec]
lemma twoSlotVec_succ (depth i j : V) :
    twoSlotVec L (depth+1) i j = qVec L (twoSlotVec L depth i j) := by
  simp [twoSlotVec]

/-- The codomain bound is deliberately loose; target i and j need not differ. -/
lemma twoSlotVec_isSemitermVec (depth i j : V) :
    IsSemitermVec L (depth+2) (depth+(i+j+1)) (twoSlotVec L depth i j) := by
  have hv : IsSemitermVec (V := V) L 2 (i+j+1) (^#i ∷ ^#j ∷ 0) := by
    have hi : i < i+j+1 := lt_of_le_of_lt le_self_add (lt_add_one _)
    have hj : j < i+j+1 := lt_of_le_of_lt le_add_self (lt_add_one _)
    simp [hi,hj]
  simpa only [twoSlotVec,add_comm] using qVecIter_isSemitermVec (L := L) hv depth

lemma twoSlotVec_spec (i j depth : V) :
    (∀ z < depth, (twoSlotVec L depth i j).[z] = ^#z) ∧
    (twoSlotVec L depth i j).[depth] = ^#(depth+i) ∧
    (twoSlotVec L depth i j).[depth+1] = ^#(depth+j) := by
  induction depth using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ depth ih =>
    have hv := twoSlotVec_isSemitermVec (L := L) depth i j
    refine ⟨?_,?_,?_⟩
    · exact qVecIter_prefix (show IsSemitermVec (V := V) L 2 (i+j+1) (^#i ∷ ^#j ∷ 0) by
        simpa only [twoSlotVec_zero,zero_add] using (twoSlotVec_isSemitermVec (L := L) 0 i j)) _
    · rw [twoSlotVec_succ]
      simp only [Bootstrapping.qVec,nth_adjoin_succ,hv.lh]
      rw [nth_termBShiftVec hv.isUTerm (by simp),ih.2.1]
      simp [add_assoc,add_comm]
    · rw [twoSlotVec_succ]
      simp only [Bootstrapping.qVec,nth_adjoin_succ,hv.lh]
      rw [nth_termBShiftVec hv.isUTerm (by simp),ih.2.2]
      simp [add_assoc,add_comm]

lemma termBindTwo_reindex {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ a b i j : V, a ≠ b →
    termSubst L (twoSlotVec L depth i j)
      (termBindOneAt L b (depth+1) (termBindOneAt L a depth term)) =
      termBindOneAt L b (depth+j) (termBindOneAt L a (depth+i) term) := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz a b i j hab
    rw [termBindOneAt_bvar,termBindOneAt_bvar,termSubst_bvar,
      (twoSlotVec_spec i j depth).1 z hz,termBindOneAt_bvar,termBindOneAt_bvar]
  · intro x a b i j hab
    classical
    by_cases hxa : x = a
    · subst x
      rw [termBindOneAt_chosen,termBindOneAt_bvar,termSubst_bvar,
        (twoSlotVec_spec i j depth).2.1,termBindOneAt_chosen,termBindOneAt_bvar]
    · by_cases hxb : x = b
      · subst x
        rw [termBindOneAt_other a depth b hab.symm,termBindOneAt_chosen,
          termSubst_bvar,(twoSlotVec_spec i j depth).2.2,
          termBindOneAt_other a (depth+i) b hab.symm,termBindOneAt_chosen]
      · rw [termBindOneAt_other a depth x hxa,termBindOneAt_other b (depth+1) x hxb,
          termSubst_fvar,termBindOneAt_other a (depth+i) x hxa,
          termBindOneAt_other b (depth+j) x hxb]
  · intro arity f terms hf hv ih a b i j hab
    have hva := termBindOneVecAt_isUTerm a depth hv.isUTerm
    have hvab := termBindOneVecAt_isUTerm b (depth+1) hva
    have hvai := termBindOneVecAt_isUTerm a (depth+i) hv.isUTerm
    rw [termBindOneAt_func a depth hf hv.isUTerm,
      termBindOneAt_func b (depth+1) hf hva,termSubst_func hf hvab,
      termBindOneAt_func a (depth+i) hf hv.isUTerm,
      termBindOneAt_func b (depth+j) hf hvai]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [hvab]
    · simp [hvai]
    · intro z hz
      rw [nth_termSubstVec hvab hz,nth_termBindOneVecAt b (depth+1) hva hz,
        nth_termBindOneVecAt a depth hv.isUTerm hz,
        nth_termBindOneVecAt b (depth+j) hvai hz,
        nth_termBindOneVecAt a (depth+i) hv.isUTerm hz]
      exact ih z hz a b i j hab

lemma termBindTwoVec_reindex {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) (a b i j : V) (hab : a ≠ b) :
    termSubstVec L arity (twoSlotVec L depth i j)
      (termBindOneVecAt L b (depth+1) arity (termBindOneVecAt L a depth arity terms)) =
      termBindOneVecAt L b (depth+j) arity (termBindOneVecAt L a (depth+i) arity terms) := by
  have hva := termBindOneVecAt_isUTerm a depth ht.isUTerm
  have hvab := termBindOneVecAt_isUTerm b (depth+1) hva
  have hvai := termBindOneVecAt_isUTerm a (depth+i) ht.isUTerm
  apply nth_ext' arity
  · simp [hvab]
  · simp [hvai]
  · intro z hz
    rw [nth_termSubstVec hvab hz,nth_termBindOneVecAt b (depth+1) hva hz,
      nth_termBindOneVecAt a depth ht.isUTerm hz,
      nth_termBindOneVecAt b (depth+j) hvai hz,
      nth_termBindOneVecAt a (depth+i) ht.isUTerm hz]
    exact termBindTwo_reindex (ht.nth hz) a b i j hab

/-- A Pi1 structural predicate: all function graphs are total Delta1, and a,b,i,j
stay universally quantified as each formula quantifier increases depth. -/
theorem bindTwo_reindex {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ a b i j : V, a ≠ b →
    subst L (twoSlotVec L depth i j)
      (bindOneAt L b (depth+1) (bindOneAt L a depth p)) =
      bindOneAt L b (depth+j) (bindOneAt L a (depth+i) p) := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ a b i j : V, a ≠ b →
    subst L (twoSlotVec L depth i j)
      (bindOneAt L b (depth+1) (bindOneAt L a depth p)) =
      bindOneAt L b (depth+j) (bindOneAt L a (depth+i) p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro depth arity R terms hR ht a b i j hab
    rw [bindOneAt_rel a depth hR ht.isUTerm,
      bindOneAt_rel b (depth+1) hR (termBindOneVecAt_isUTerm a depth ht.isUTerm),
      substs_rel hR (termBindOneVecAt_isUTerm b (depth+1)
        (termBindOneVecAt_isUTerm a depth ht.isUTerm)),
      termBindTwoVec_reindex ht a b i j hab,
      bindOneAt_rel a (depth+i) hR ht.isUTerm,
      bindOneAt_rel b (depth+j) hR (termBindOneVecAt_isUTerm a (depth+i) ht.isUTerm)]
  · intro depth arity R terms hR ht a b i j hab
    rw [bindOneAt_nrel a depth hR ht.isUTerm,
      bindOneAt_nrel b (depth+1) hR (termBindOneVecAt_isUTerm a depth ht.isUTerm),
      substs_nrel hR (termBindOneVecAt_isUTerm b (depth+1)
        (termBindOneVecAt_isUTerm a depth ht.isUTerm)),
      termBindTwoVec_reindex ht a b i j hab,
      bindOneAt_nrel a (depth+i) hR ht.isUTerm,
      bindOneAt_nrel b (depth+j) hR (termBindOneVecAt_isUTerm a (depth+i) ht.isUTerm)]
  · intro depth a b i j hab; simp
  · intro depth a b i j hab; simp
  · intro depth p q hp hq ihp ihq a b i j hab
    rw [bindOneAt_and a depth hp.isUFormula hq.isUFormula,
      bindOneAt_and b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula
        (bindOneAt_isSemiformula hq a).isUFormula,
      substs_and (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp a) b).isUFormula
        (bindOneAt_isSemiformula (bindOneAt_isSemiformula hq a) b).isUFormula,
      ihp a b i j hab,ihq a b i j hab,
      bindOneAt_and a (depth+i) hp.isUFormula hq.isUFormula,
      bindOneAt_and b (depth+j) (bindOne_offset_isUFormula hp a i)
        (bindOne_offset_isUFormula hq a i)]
  · intro depth p q hp hq ihp ihq a b i j hab
    rw [bindOneAt_or a depth hp.isUFormula hq.isUFormula,
      bindOneAt_or b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula
        (bindOneAt_isSemiformula hq a).isUFormula,
      substs_or (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp a) b).isUFormula
        (bindOneAt_isSemiformula (bindOneAt_isSemiformula hq a) b).isUFormula,
      ihp a b i j hab,ihq a b i j hab,
      bindOneAt_or a (depth+i) hp.isUFormula hq.isUFormula,
      bindOneAt_or b (depth+j) (bindOne_offset_isUFormula hp a i)
        (bindOne_offset_isUFormula hq a i)]
  · intro depth p hp ih a b i j hab
    rw [bindOneAt_all a depth hp.isUFormula,
      bindOneAt_all b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula,
      substs_all (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp a) b).isUFormula,
      ←twoSlotVec_succ,ih a b i j hab,
      bindOneAt_all a (depth+i) hp.isUFormula,
      bindOneAt_all b (depth+j) (by
        simpa only [add_assoc,add_comm,add_left_comm] using bindOne_offset_isUFormula hp a i)]
    ac_rfl
  · intro depth p hp ih a b i j hab
    rw [bindOneAt_exs a depth hp.isUFormula,
      bindOneAt_exs b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula,
      substs_ex (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp a) b).isUFormula,
      ←twoSlotVec_succ,ih a b i j hab,
      bindOneAt_exs a (depth+i) hp.isUFormula,
      bindOneAt_exs b (depth+j) (by
        simpa only [add_assoc,add_comm,add_left_comm] using bindOne_offset_isUFormula hp a i)]
    ac_rfl

end LeanProofs.ZFCinPA.ModelCodedBindTwoSlots
