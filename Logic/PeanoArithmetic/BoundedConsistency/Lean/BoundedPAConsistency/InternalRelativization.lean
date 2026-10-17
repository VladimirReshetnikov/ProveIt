import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
Represented relativization of internal formulas to a definable class.

Fix an internal formula code `d` with one bound variable `#0` (the domain
formula `δ(x)`). The relativization `relativize L d p` of an internal formula
code `p` (in negation normal form, as Foundation codes formulas) leaves atoms
and the propositional connectives unchanged and guards every quantifier:

    ∀ q  ↦  ∀ (¬δ(#0) ∨ q^δ),        ∃ q  ↦  ∃ (δ(#0) ∧ q^δ).

It is one `UformulaRec1` construction with `d` as the recursion parameter,
hence a total Σ₁-definable function in every model of IΣ₁, defined at every
internal code (nonstandard ones included). This module proves its constructor
equations and that it preserves well-formed (semi)formulas; the commutation
with negation, shift and substitution and the transport of internal
derivations follow in later sections.

This is the represented counterpart of a relative interpretation's formula
translation (`LO.FirstOrder.DirectTranslation` is the external one). It is the
syntactic core of the PA-internal proof transports needed for the
ZF/ZFC comparison through `L` and for the well-founded-part comparison.
-/
namespace LeanProofs.BoundedPAConsistency.InternalRelativization

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace Relativization

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !qqRelDef y k R v”
  nrel := .mkSigma “y param k R v. !qqNRelDef y k R v”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. ∃ nd, !(negGraph L) nd param ∧ ∃ z, !qqOrDef z nd y₁ ∧ !qqAllDef y z”
  exs := .mkSigma “y param p₁ y₁. ∃ z, !qqAndDef z param y₁ ∧ !qqExsDef y z”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel := fun _ k R v ↦ ^rel k R v
  nrel := fun _ k R v ↦ ^nrel k R v
  verum := fun _ ↦ ^⊤
  falsum := fun _ ↦ ^⊥
  and := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all := fun d _ y₁ ↦ ^∀ (neg L d ^⋎ y₁)
  exs := fun d _ y₁ ↦ ^∃ (d ^⋏ y₁)
  allChanges := fun d ↦ d
  exsChanges := fun d ↦ d
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end Relativization

open Relativization

variable (L)

/-- Relativization of the internal formula `p` to the class defined by `d`. -/
noncomputable def relativize (d p : V) : V := (construction L).result L d p

noncomputable def relativizeGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L

variable {L}

instance relativize.defined : 𝚺₁-Function₂[V] relativize L via relativizeGraph L :=
  (construction L).result_defined

instance relativize.definable : 𝚺₁-Function₂[V] relativize L := relativize.defined.to_definable

instance relativize.definable' : Γ-[m + 1]-Function₂[V] relativize L :=
  relativize.definable.of_sigmaOne

section Equations

variable {d : V}

@[simp] lemma relativize_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    relativize L d (^rel k R v) = ^rel k R v := by
  simp [relativize, hR, hv, construction]

@[simp] lemma relativize_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    relativize L d (^nrel k R v) = ^nrel k R v := by
  simp [relativize, hR, hv, construction]

@[simp] lemma relativize_verum : relativize L d (^⊤ : V) = ^⊤ := by
  simp [relativize, construction]

@[simp] lemma relativize_falsum : relativize L d (^⊥ : V) = ^⊥ := by
  simp [relativize, construction]

@[simp] lemma relativize_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    relativize L d (p ^⋏ q) = relativize L d p ^⋏ relativize L d q := by
  simp [relativize, hp, hq, construction]

@[simp] lemma relativize_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    relativize L d (p ^⋎ q) = relativize L d p ^⋎ relativize L d q := by
  simp [relativize, hp, hq, construction]

@[simp] lemma relativize_all {p : V} (hp : IsUFormula L p) :
    relativize L d (^∀ p) = ^∀ (neg L d ^⋎ relativize L d p) := by
  simp [relativize, hp, construction]

@[simp] lemma relativize_exs {p : V} (hp : IsUFormula L p) :
    relativize L d (^∃ p) = ^∃ (d ^⋏ relativize L d p) := by
  simp [relativize, hp, construction]

lemma relativize_not_uformula {x : V} (h : ¬IsUFormula L x) : relativize L d x = 0 :=
  (construction L).result_prop_not _ h

end Equations

section Laws

variable {d : V}

lemma isUFormula_relativize (hd : IsUFormula L d) {p : V} :
    IsUFormula L p → IsUFormula L (relativize L d p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp, hd]
  · intro p hp ihp; simp [hp, ihp, hd]

lemma isSemiformula_of_one {n : V} (h : IsSemiformula L 1 d) : IsSemiformula L (n + 1) d :=
  ⟨h.isUFormula, le_trans h.bv_le (by simp)⟩

lemma isSemiformula_relativize (hd : IsSemiformula L 1 d) {n p : V} :
    IsSemiformula L n p → IsSemiformula L n (relativize L d p) := by
  apply IsSemiformula.sigma1_structural_induction
  · definability
  · intro n k r v hr hv; simp [hr, hv, hv.isUTerm]
  · intro n k r v hr hv; simp [hr, hv, hv.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp.isUFormula, ihp, (isSemiformula_of_one hd)]
  · intro n p hp ihp; simp [hp.isUFormula, ihp, (isSemiformula_of_one hd)]

/-- Relativization commutes with negation. -/
lemma relativize_neg (hd : IsUFormula L d) {p : V} :
    IsUFormula L p → neg L (relativize L d p) = relativize L d (neg L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, (isUFormula_relativize hd hp), (isUFormula_relativize hd hq), hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq
    simp [hp, hq, (isUFormula_relativize hd hp), (isUFormula_relativize hd hq), hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp
    simp [hp, (isUFormula_relativize hd hp), hp.neg, hd, hd.neg, ihp]
  · intro p hp ihp
    simp [hp, (isUFormula_relativize hd hp), hp.neg, hd, ihp]

/-- Relativization to a shift-fixed domain formula commutes with the shift of
free variables. -/
lemma relativize_shift (hd : IsSemiformula L 1 d) (hds : shift L d = d) {p : V} :
    IsUFormula L p → shift L (relativize L d p) = relativize L d (shift L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv, hv.termShiftVec]
  · intro k r v hr hv; simp [hr, hv, hv.termShiftVec]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, (isUFormula_relativize hd.isUFormula hp), (isUFormula_relativize hd.isUFormula hq), hp.shift, hq.shift,
      ihp, ihq]
  · intro p q hp hq ihp ihq
    simp [hp, hq, (isUFormula_relativize hd.isUFormula hp), (isUFormula_relativize hd.isUFormula hq), hp.shift, hq.shift,
      ihp, ihq]
  · intro p hp ihp
    simp [hp, (isUFormula_relativize hd.isUFormula hp), hp.shift, hd.isUFormula.neg, ihp,
      shift_neg hd, hds]
  · intro p hp ihp
    simp [hp, (isUFormula_relativize hd.isUFormula hp), hp.shift, hd.isUFormula, ihp, hds]

end Laws

section Subst

/-- Substitution fixes a semiformula of arity `k` whenever the first `k`
entries of the (possibly longer) vector are the bound variables themselves.
Foundation's `subst_eq_self` asks for a vector of length exactly `k`. -/
lemma subst_eq_self_of_prefix {k p : V} (hp : IsSemiformula L k p) :
    ∀ {m a w : V}, IsSemitermVec L m a w → k ≤ m → (∀ i < k, w.[i] = ^#i) → subst L w p = p := by
  suffices h : ∀ m a w : V, IsSemitermVec L m a w → k ≤ m → (∀ i < k, w.[i] = ^#i) →
      subst L w p = p from fun {m a w} hw hk H => h m a w hw hk H
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro k K R v hR hv m a w _ _ H
    simp only [substs_rel hR hv.isUTerm, qqRel_inj, true_and]
    apply nth_ext' K (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro k K R v hR hv m a w _ _ H
    simp only [substs_nrel hR hv.isUTerm, qqNRel_inj, true_and]
    apply nth_ext' K (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro k m a w _ _ _; simp
  · intro k m a w _ _ _; simp
  · intro k p q hp hq ihp ihq m a w hw hk H
    simp [hp.isUFormula, hq.isUFormula, ihp m a w hw hk H, ihq m a w hw hk H]
  · intro k p q hp hq ihp ihq m a w hw hk H
    simp [hp.isUFormula, hq.isUFormula, ihp m a w hw hk H, ihq m a w hw hk H]
  · intro k p hp ih m a w hw hk H
    have H' : ∀ i < k + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < k := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm)
          (by simpa [hw.lh] using lt_of_lt_of_le hi hk)]
        simp [H i hi]
    simp [hp.isUFormula, ih (m + 1) (a + 1) (qVec L w) hw.qVec (by simpa using hk) H']
  · intro k p hp ih m a w hw hk H
    have H' : ∀ i < k + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < k := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm)
          (by simpa [hw.lh] using lt_of_lt_of_le hi hk)]
        simp [H i hi]
    simp [hp.isUFormula, ih (m + 1) (a + 1) (qVec L w) hw.qVec (by simpa using hk) H']

variable {d : V}

/-- The domain formula is fixed by every substitution under a binder. -/
lemma subst_qVec_domain (hd : IsSemiformula L 1 d) {n a w : V} (hw : IsSemitermVec L n a w) :
    subst L (qVec L w) d = d :=
  subst_eq_self_of_prefix hd hw.qVec (by simp) (by
    intro i hi
    have : i = 0 := by simpa using hi
    subst this; simp [qVec])

/-- Relativization commutes with substitution of terms for bound variables. -/
lemma relativize_subst (hd : IsSemiformula L 1 d) {n p : V} (hp : IsSemiformula L n p) :
    ∀ {a w : V}, IsSemitermVec L n a w →
      subst L w (relativize L d p) = relativize L d (subst L w p) := by
  suffices h : ∀ a w : V, IsSemitermVec L n a w →
      subst L w (relativize L d p) = relativize L d (subst L w p) from fun {a w} hw => h a w hw
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv a w hw
    rw [relativize_rel hR hv.isUTerm, substs_rel hR hv.isUTerm,
      relativize_rel hR (hw.termSubstVec hv).isUTerm]
  · intro n k R v hR hv a w hw
    rw [relativize_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm,
      relativize_nrel hR (hw.termSubstVec hv).isUTerm]
  · intro n a w _; simp
  · intro n a w _; simp
  · intro n p q hp hq ihp ihq a w hw
    rw [relativize_and hp.isUFormula hq.isUFormula,
      substs_and (isUFormula_relativize hd.isUFormula hp.isUFormula)
        (isUFormula_relativize hd.isUFormula hq.isUFormula),
      substs_and hp.isUFormula hq.isUFormula,
      relativize_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula, ihp a w hw, ihq a w hw]
  · intro n p q hp hq ihp ihq a w hw
    rw [relativize_or hp.isUFormula hq.isUFormula,
      substs_or (isUFormula_relativize hd.isUFormula hp.isUFormula)
        (isUFormula_relativize hd.isUFormula hq.isUFormula),
      substs_or hp.isUFormula hq.isUFormula,
      relativize_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula, ihp a w hw, ihq a w hw]
  · intro n p hp ih a w hw
    have hd' : IsSemiformula L (n + 1) d := isSemiformula_of_one hd
    rw [relativize_all hp.isUFormula,
      substs_all (by simp [hd.isUFormula, isUFormula_relativize hd.isUFormula hp.isUFormula]),
      substs_or hd.isUFormula.neg (isUFormula_relativize hd.isUFormula hp.isUFormula),
      substs_neg hd' hw.qVec, subst_qVec_domain hd hw,
      substs_all hp.isUFormula, relativize_all (hp.subst hw.qVec).isUFormula,
      ih (a + 1) (qVec L w) hw.qVec]
  · intro n p hp ih a w hw
    rw [relativize_exs hp.isUFormula,
      substs_ex (by simp [hd.isUFormula, isUFormula_relativize hd.isUFormula hp.isUFormula]),
      substs_and hd.isUFormula (isUFormula_relativize hd.isUFormula hp.isUFormula),
      subst_qVec_domain hd hw,
      substs_ex hp.isUFormula, relativize_exs (hp.subst hw.qVec).isUFormula,
      ih (a + 1) (qVec L w) hw.qVec]

lemma relativize_substs1 (hd : IsSemiformula L 1 d) {n t p : V} (ht : IsSemiterm L n t)
    (hp : IsSemiformula L 1 p) :
    substs1 L t (relativize L d p) = relativize L d (substs1 L t p) :=
  relativize_subst hd hp (show IsSemitermVec L 1 n ?[t] by simp [ht])

lemma relativize_free (hd : IsSemiformula L 1 d) (hds : shift L d = d) {p : V}
    (hp : IsSemiformula L 1 p) :
    free L (relativize L d p) = relativize L d (free L p) := by
  simp only [free]
  rw [relativize_shift hd hds hp.isUFormula,
    relativize_substs1 hd (show IsSemiterm L 0 (^&0 : V) by simp) hp.shift]

end Subst

end LeanProofs.BoundedPAConsistency.InternalRelativization
