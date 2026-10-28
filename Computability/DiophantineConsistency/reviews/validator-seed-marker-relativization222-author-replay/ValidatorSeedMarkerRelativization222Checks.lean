import ZFCinPA.ValidatorSeedMarkerRelativization222

set_option autoImplicit false
set_option Elab.async false
namespace LeanProofs.ZFCinPA.ValidatorSeedMarkerRelativization222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open ValidatorSeedMarkerRelativization222 ValidatorSeedMarkerDischarge222
open ValidatorFullSeedTheory222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : SetTheory} [T.Δ₁]

example : 𝚺₁-Function₂[V] taggedSeq := taggedSeq_definable
example (j : V) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    IsSemiformula ℒₛₑₜ n (tagRel j p) := tagRel_typed j hp
example (j : V) {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    free ℒₛₑₜ (tagRel j p)=tagRel (j+1) (free ℒₛₑₜ p) := tagRel_free j hp
-- Nested binders retain the changing marker and arbitrary free parameters.
example (j : V) {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p) :
    shift ℒₛₑₜ (tagRel j (^∀ (^∃ p)))=
      tagRel (j+1) (shift ℒₛₑₜ (^∀ (^∃ p))) :=
  tagRel_shift j (by simp [hp.isUFormula])
example (j : V) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    taggedSeq (j+1) (setShift ℒₛₑₜ s)=
      insert (free ℒₛₑₜ (neg ℒₛₑₜ (domainCode j))) (setShift ℒₛₑₜ (taggedSeq j s)) :=
  taggedSeq_succ j hs
example {t : V} (ht : IsTerm ℒₛₑₜ t) : ∃ i : V, t=^&i := term_eq_fvar ht
example {s p i dp j : V} (hj : exsIntro s p (^&i) dp<j) : i<j := exs_label_bound hj
example {child parent j B : V} (hc : child<parent) (hb : parent+j≤B) :
    child+(j+1)≤B := all_child_budget hc hb
example {child parent k : V} (hc : child<parent) (hj : parent<k+1) : child<k :=
  predecessor_child_bound hc hj
example (hAx : AxiomImages T V) {der j : V} (hd : Derivation T der) (hj : der<j) :
    Derivable seedTheory (taggedSeq j (fstIdx der)) := derivable_tagged hAx hd hj
example : taggedSeq (0:V) (insert (^⊥ : V) ∅)=residual (0:V) := taggedSeq_falsum 0
example (hAx : ∀ p j : V, IsFormula ℒₛₑₜ p → p∈T.Δ₁Class → p<j →
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j))))
    (h : Provable T (^⊥ : V)) : Provable seedTheory (^⊥ : V) :=
  provable_falsum_of_tagged hAx h
example [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] (hAx : AxiomImages T V) (h : Provable T (^⊥ : V)) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d=2 :=
  refutation_witness hAx h

#print axioms tagRel_typed
#print axioms tagRel_subst
#print axioms tagRel_shift
#print axioms tagRel_free
#print axioms tagSet_shift
#print axioms taggedSeq_succ
#print axioms term_eq_fvar
#print axioms exs_label_bound
#print axioms all_child_budget
#print axioms predecessor_child_bound
#print axioms derivable_tagged_bounded
#print axioms derivable_tagged
#print axioms taggedSeq_falsum
#print axioms provable_falsum_of_tagged
#print axioms ValidatorSeedMarkerRelativization222.refutation_witness
end LeanProofs.ZFCinPA.ValidatorSeedMarkerRelativization222Checks
