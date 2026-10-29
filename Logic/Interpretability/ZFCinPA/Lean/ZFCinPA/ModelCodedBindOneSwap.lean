import ZFCinPA.ModelCodedBindOne
import ZFCinPA.ModelCodedBindTwoSlots

set_option autoImplicit false

/-!
Internal exchange of two distinct named binders. The existing arbitrary bound
depth is retained, while the two new bound slots are swapped by a represented
qVec iteration. Every label, depth and matrix code is internal; no finite
standard support or closed-matrix premise occurs. Equal labels are intentionally
excluded from this swap identity and handled separately by numerical clients.
-/
namespace LeanProofs.ZFCinPA.ModelCodedBindOneSwap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def swapVec (L : Language) [L.Encodable] [L.LORDefinable]
    (depth : V) : V := qVecIter L depth (^#1 ∷ ^#0 ∷ 0)
noncomputable def swapVecDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 2 := .mkSigma “out depth.
      ∃ b0, !qqBvarDef b0 0 ∧ ∃ b1, !qqBvarDef b1 1 ∧
      ∃ v0, !adjoinDef v0 b0 0 ∧ ∃ v, !adjoinDef v b1 v0 ∧
      !(qVecIterDef L) out depth v”
instance swapVec_defined : 𝚺₁-Function₁[V] (swapVec L) via swapVecDef L :=
  .mk fun e => by simp [swapVecDef,swapVec]
private instance swapVec_delta : 𝚫₁-Function₁[V] (swapVec L) :=
  swapVec_defined.graph_delta.to_definable
private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance termBindOneVecAt_delta : 𝚫₁-Function₄[V] (termBindOneVecAt L) :=
  termBindOneVecAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

@[simp] lemma swapVec_zero : swapVec (V := V) L 0 = ^#1 ∷ ^#0 ∷ 0 := by
  simp [swapVec]
lemma swapVec_succ (depth : V) : swapVec L (depth+1) = qVec L (swapVec L depth) := by
  simp [swapVec]
lemma swapVec_isSemitermVec (depth : V) :
    IsSemitermVec L (depth+2) (depth+2) (swapVec L depth) := by
  simpa only [swapVec,add_comm] using qVecIter_isSemitermVec (L := L)
    (show IsSemitermVec (V := V) L 2 2 (^#1 ∷ ^#0 ∷ 0) by simp) depth

lemma swapVec_spec (depth : V) :
    (∀ i < depth, (swapVec L depth).[i] = ^#i) ∧
    (swapVec L depth).[depth] = ^#(depth+1) ∧
    (swapVec L depth).[depth+1] = ^#depth := by
  simpa only [swapVec, ModelCodedBindTwoSlots.twoSlotVec, add_zero] using
    (ModelCodedBindTwoSlots.twoSlotVec_spec (L := L) (1 : V) 0 depth)

lemma termBindOneAt_swap {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ a b : V, a ≠ b →
    termSubst L (swapVec L depth)
      (termBindOneAt L a (depth+1) (termBindOneAt L b depth term)) =
      termBindOneAt L b (depth+1) (termBindOneAt L a depth term) := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz a b hab
    rw [termBindOneAt_bvar,termBindOneAt_bvar,termBindOneAt_bvar,
      termBindOneAt_bvar,termSubst_bvar]
    exact (swapVec_spec depth).1 z hz
  · intro x a b hab
    classical
    by_cases hxb : x = b
    · subst x
      rw [termBindOneAt_chosen,termBindOneAt_bvar,termSubst_bvar,
        (swapVec_spec depth).2.1,termBindOneAt_other a depth b hab.symm,
        termBindOneAt_chosen]
    · by_cases hxa : x = a
      · subst x
        rw [termBindOneAt_other b depth a hab,termBindOneAt_chosen,
          termSubst_bvar,(swapVec_spec depth).2.2,
          termBindOneAt_chosen,termBindOneAt_bvar]
      · rw [termBindOneAt_other b depth x hxb,termBindOneAt_other a (depth+1) x hxa,
          termSubst_fvar,termBindOneAt_other a depth x hxa,
          termBindOneAt_other b (depth+1) x hxb]
  · intro arity f terms hf hv ih a b hab
    have hvb := termBindOneVecAt_isUTerm b depth hv.isUTerm
    have hva := termBindOneVecAt_isUTerm a depth hv.isUTerm
    have hvba := termBindOneVecAt_isUTerm a (depth+1) hvb
    rw [termBindOneAt_func b depth hf hv.isUTerm,
      termBindOneAt_func a (depth+1) hf hvb,
      termSubst_func hf hvba,
      termBindOneAt_func a depth hf hv.isUTerm,
      termBindOneAt_func b (depth+1) hf hva]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [hvba]
    · simp [hva]
    · intro i hi
      rw [nth_termSubstVec hvba hi,nth_termBindOneVecAt a (depth+1) hvb hi,
        nth_termBindOneVecAt b depth hv.isUTerm hi,
        nth_termBindOneVecAt b (depth+1) hva hi,
        nth_termBindOneVecAt a depth hv.isUTerm hi]
      exact ih i hi a b hab

lemma termBindOneVecAt_swap {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) (a b : V) (hab : a ≠ b) :
    termSubstVec L arity (swapVec L depth)
      (termBindOneVecAt L a (depth+1) arity (termBindOneVecAt L b depth arity terms)) =
      termBindOneVecAt L b (depth+1) arity (termBindOneVecAt L a depth arity terms) := by
  have hvb := termBindOneVecAt_isUTerm b depth ht.isUTerm
  have hva := termBindOneVecAt_isUTerm a depth ht.isUTerm
  have hvba := termBindOneVecAt_isUTerm a (depth+1) hvb
  apply nth_ext' arity
  · simp [hvba]
  · simp [hva]
  · intro i hi
    rw [nth_termSubstVec hvba hi,nth_termBindOneVecAt a (depth+1) hvb hi,
      nth_termBindOneVecAt b depth ht.isUTerm hi,
      nth_termBindOneVecAt b (depth+1) hva hi,
      nth_termBindOneVecAt a depth ht.isUTerm hi]
    exact termBindOneAt_swap (ht.nth hi) a b hab

lemma bindOneAt_swap {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ a b : V, a ≠ b →
    subst L (swapVec L depth) (bindOneAt L a (depth+1) (bindOneAt L b depth p)) =
      bindOneAt L b (depth+1) (bindOneAt L a depth p) := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ a b : V, a ≠ b →
    subst L (swapVec L depth) (bindOneAt L a (depth+1) (bindOneAt L b depth p)) =
      bindOneAt L b (depth+1) (bindOneAt L a depth p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro depth arity R terms hR ht a b hab
    rw [bindOneAt_rel b depth hR ht.isUTerm,
      bindOneAt_rel a (depth+1) hR (termBindOneVecAt_isUTerm b depth ht.isUTerm),
      substs_rel hR (termBindOneVecAt_isUTerm a (depth+1)
        (termBindOneVecAt_isUTerm b depth ht.isUTerm)),
      termBindOneVecAt_swap ht a b hab,bindOneAt_rel a depth hR ht.isUTerm,
      bindOneAt_rel b (depth+1) hR (termBindOneVecAt_isUTerm a depth ht.isUTerm)]
  · intro depth arity R terms hR ht a b hab
    rw [bindOneAt_nrel b depth hR ht.isUTerm,
      bindOneAt_nrel a (depth+1) hR (termBindOneVecAt_isUTerm b depth ht.isUTerm),
      substs_nrel hR (termBindOneVecAt_isUTerm a (depth+1)
        (termBindOneVecAt_isUTerm b depth ht.isUTerm)),
      termBindOneVecAt_swap ht a b hab,bindOneAt_nrel a depth hR ht.isUTerm,
      bindOneAt_nrel b (depth+1) hR (termBindOneVecAt_isUTerm a depth ht.isUTerm)]
  · intro depth a b hab; simp
  · intro depth a b hab; simp
  · intro depth p q hp hq ihp ihq a b hab
    rw [bindOneAt_and b depth hp.isUFormula hq.isUFormula,
      bindOneAt_and a (depth+1) (bindOneAt_isSemiformula hp b).isUFormula
        (bindOneAt_isSemiformula hq b).isUFormula,
      substs_and (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp b) a).isUFormula
        (bindOneAt_isSemiformula (bindOneAt_isSemiformula hq b) a).isUFormula,
      ihp a b hab,ihq a b hab,bindOneAt_and a depth hp.isUFormula hq.isUFormula,
      bindOneAt_and b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula
        (bindOneAt_isSemiformula hq a).isUFormula]
  · intro depth p q hp hq ihp ihq a b hab
    rw [bindOneAt_or b depth hp.isUFormula hq.isUFormula,
      bindOneAt_or a (depth+1) (bindOneAt_isSemiformula hp b).isUFormula
        (bindOneAt_isSemiformula hq b).isUFormula,
      substs_or (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp b) a).isUFormula
        (bindOneAt_isSemiformula (bindOneAt_isSemiformula hq b) a).isUFormula,
      ihp a b hab,ihq a b hab,bindOneAt_or a depth hp.isUFormula hq.isUFormula,
      bindOneAt_or b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula
        (bindOneAt_isSemiformula hq a).isUFormula]
  · intro depth p hp ih a b hab
    rw [bindOneAt_all b depth hp.isUFormula,
      bindOneAt_all a (depth+1) (bindOneAt_isSemiformula hp b).isUFormula,
      substs_all (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp b) a).isUFormula,
      ←swapVec_succ,ih a b hab,bindOneAt_all a depth hp.isUFormula,
      bindOneAt_all b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula]
  · intro depth p hp ih a b hab
    rw [bindOneAt_exs b depth hp.isUFormula,
      bindOneAt_exs a (depth+1) (bindOneAt_isSemiformula hp b).isUFormula,
      substs_ex (bindOneAt_isSemiformula (bindOneAt_isSemiformula hp b) a).isUFormula,
      ←swapVec_succ,ih a b hab,bindOneAt_exs a depth hp.isUFormula,
      bindOneAt_exs b (depth+1) (bindOneAt_isSemiformula hp a).isUFormula]

end LeanProofs.ZFCinPA.ModelCodedBindOneSwap
