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
internal code (nonstandard ones included). The module proves, in every model
of IΣ₁:

* the constructor equations, preservation of well-formed (semi)formulas, and
  commutation with negation, shift (for shift-fixed `d`) and substitution;
* `derivable_relSet`: every internal T-derivation of a sequent `s` yields a
  U-derivation of `s^δ` with side formulas `¬δ(&i)`, `i < m`, given U-proofs
  of the relativized T-axioms and that closed terms are free variables;
* `derivable_of_domSet`: the side formulas are discharged from `U ⊢ ∃x δ(x)`;
* `provable_relativize` and `provable_falsum_of_relativize`: the internal
  relative-interpretation theorem, and `Prov_T(⊥) → Prov_U(⊥)`.

The interpretation-specific axiom obligations (for `L`, `ZF ⊢ ax^L` at every
internal ZFC axiom code) are not part of this module.

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

/-! ### Relativized sequents and domain side formulas -/

section Sets

variable (L)

/-- `¬δ(&i)`: the domain formula at the free variable `&i`, negated. -/
noncomputable def domF (d i : V) : V := neg L (substs1 L ^&i d)

variable {L}

instance domF.definable : 𝚺₁-Function₂[V] domF L := by
  unfold domF; definability

lemma relSet_existsUnique (d s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = relativize L d x :=
  sigma₁_replacement (by definability) s

lemma domSet_existsUnique (d m : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ i ∈ under m, y = domF L d i :=
  sigma₁_replacement (by definability) (under m)

variable (L)

/-- The relativized sequent `s^δ`. -/
noncomputable def relSet (d s : V) : V := Classical.choose! (relSet_existsUnique (L := L) d s)

/-- The side formulas `{¬δ(&i) | i < m}`. -/
noncomputable def domSet (d m : V) : V := Classical.choose! (domSet_existsUnique (L := L) d m)

variable {L}

lemma mem_relSet_iff {d s y : V} : y ∈ relSet L d s ↔ ∃ x ∈ s, y = relativize L d x :=
  Classical.choose!_spec (relSet_existsUnique (L := L) d s) y

lemma mem_domSet_iff {d m y : V} : y ∈ domSet L d m ↔ ∃ i < m, y = domF L d i := by
  rw [domSet, Classical.choose!_spec (domSet_existsUnique (L := L) d m) y]
  simp

instance relSet.definable : 𝚺₁-Function₂[V] relSet L := by
  apply HierarchySymbol.Definable.of_iff
    (Q := fun v ↦ (∀ y ∈ v 0, ∃ x ∈ v 2, y = relativize L (v 1) x) ∧
      (∀ x ∈ v 2, relativize L (v 1) x ∈ v 0))
  · definability
  · intro v
    constructor
    · intro h
      simp only [Fin.isValue] at h
      rw [h]
      exact ⟨fun y hy => mem_relSet_iff.mp hy, fun x hx => mem_relSet_iff.mpr ⟨x, hx, rfl⟩⟩
    · rintro ⟨h₁, h₂⟩
      apply mem_ext; intro y
      constructor
      · intro hy; exact mem_relSet_iff.mpr (h₁ y hy)
      · intro hy
        obtain ⟨x, hx, rfl⟩ := mem_relSet_iff.mp hy
        exact h₂ x hx

instance domSet.definable : 𝚺₁-Function₂[V] domSet L := by
  apply HierarchySymbol.Definable.of_iff
    (Q := fun v ↦ (∀ y ∈ v 0, ∃ i < v 2, y = domF L (v 1) i) ∧ (∀ i < v 2, domF L (v 1) i ∈ v 0))
  · definability
  · intro v
    constructor
    · intro h
      simp only [Fin.isValue] at h
      rw [h]
      exact ⟨fun y hy => mem_domSet_iff.mp hy, fun i hi => mem_domSet_iff.mpr ⟨i, hi, rfl⟩⟩
    · rintro ⟨h₁, h₂⟩
      apply mem_ext; intro y
      constructor
      · intro hy; exact mem_domSet_iff.mpr (h₁ y hy)
      · intro hy
        obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
        exact h₂ i hi

variable {d : V}

lemma relSet_insert {x s : V} : relSet L d (insert x s) = insert (relativize L d x) (relSet L d s) :=
  mem_ext fun y => by simp [mem_relSet_iff]

lemma relSet_subset {s s' : V} (h : s ⊆ s') : relSet L d s ⊆ relSet L d s' := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_relSet_iff.mp hy
  exact mem_relSet_iff.mpr ⟨x, h hx, rfl⟩

lemma domSet_subset {m m' : V} (h : m ≤ m') : domSet L d m ⊆ domSet L d m' := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
  exact mem_domSet_iff.mpr ⟨i, lt_of_lt_of_le hi h, rfl⟩

lemma relativize_mem_relSet {x s : V} (h : x ∈ s) : relativize L d x ∈ relSet L d s :=
  mem_relSet_iff.mpr ⟨x, h, rfl⟩

lemma domF_mem_domSet {i m : V} (h : i < m) : domF L d i ∈ domSet L d m :=
  mem_domSet_iff.mpr ⟨i, h, rfl⟩

lemma isFormula_domF (hd : IsSemiformula L 1 d) (i : V) : IsFormula L (domF L d i) := by
  simp only [domF]
  exact (hd.substs1 (by simp)).neg

lemma isFormulaSet_relSet (hd : IsSemiformula L 1 d) {s : V} (hs : IsFormulaSet L s) :
    IsFormulaSet L (relSet L d s) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_relSet_iff.mp hy
  exact isSemiformula_relativize hd (hs x hx)

lemma isFormulaSet_domSet (hd : IsSemiformula L 1 d) (m : V) : IsFormulaSet L (domSet L d m) := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := mem_domSet_iff.mp hy
  exact isFormula_domF hd i

lemma shift_domF (hd : IsSemiformula L 1 d) (hds : shift L d = d) (i : V) :
    shift L (domF L d i) = domF L d (i + 1) := by
  simp only [domF]
  rw [shift_neg (hd.substs1 (show IsSemiterm L 0 (^&i : V) by simp))]
  simp only [substs1]
  rw [shift_substs hd (show IsSemitermVec L 1 0 ?[(^&i : V)] by simp), hds]
  simp

lemma setShift_relSet (hd : IsSemiformula L 1 d) (hds : shift L d = d) {s : V}
    (hs : IsFormulaSet L s) : setShift L (relSet L d s) = relSet L d (setShift L s) :=
  mem_ext fun y => by
    simp only [mem_setShift_iff, mem_relSet_iff]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨shift L x, ⟨x, hx, rfl⟩, relativize_shift hd hds (hs x hx).isUFormula⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨relativize L d x, ⟨x, hx, rfl⟩, (relativize_shift hd hds (hs x hx).isUFormula).symm⟩

lemma setShift_domSet_subset (hd : IsSemiformula L 1 d) (hds : shift L d = d) (m : V) :
    setShift L (domSet L d m) ⊆ domSet L d (m + 1) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_setShift_iff.mp hy
  obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hz
  rw [shift_domF hd hds]
  exact domF_mem_domSet (by simpa using hi)

/-- `{¬δ(&i) | i < m}` lies in `¬δ(&0)` together with the shift of itself. -/
lemma domSet_subset_insert_setShift (hd : IsSemiformula L 1 d) (hds : shift L d = d) (m : V) :
    domSet L d m ⊆ insert (domF L d 0) (setShift L (domSet L d m)) := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
  rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
  · simp
  · refine mem_bitInsert_iff.mpr (Or.inr (mem_setShift_iff.mpr ⟨domF L d j, ?_, ?_⟩))
    · exact domF_mem_domSet (lt_of_le_of_lt (by simp) hi)
    · exact (shift_domF hd hds j).symm

end Sets

/-! ### Transport of internal derivations -/

section Helpers

variable {d : V}

lemma free_or {p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q) :
    free L (p ^⋎ q) = free L p ^⋎ free L q := by
  simp only [free, substs1]
  rw [shift_or hp.isUFormula hq.isUFormula,
    substs_or hp.shift.isUFormula hq.shift.isUFormula]

lemma free_neg_domain (hd : IsSemiformula L 1 d) (hds : shift L d = d) :
    free L (neg L d) = domF L d 0 := by
  simp only [free, domF]
  rw [shift_neg hd, hds]
  simp only [substs1]
  rw [substs_neg hd (show IsSemitermVec L 1 0 ?[(^&0 : V)] by simp)]

/-- Weaken a relativized derivation of `insert x s` to `insert x^δ` over `s^δ`
with more side formulas. -/
lemma derivable_insert_of_relSet {U : Theory L} [U.Δ₁] {x s m m' : V} (hm : m ≤ m')
    (hT : IsFormulaSet L (insert (relativize L d x) (relSet L d s ∪ domSet L d m')))
    (h : Derivable U (relSet L d (insert x s) ∪ domSet L d m)) :
    Derivable U (insert (relativize L d x) (relSet L d s ∪ domSet L d m')) := by
  refine Derivable.wk hT ?_ h
  intro y hy
  rcases mem_cup_iff.mp hy with hy | hy
  · rw [relSet_insert] at hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hy)))
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr (domSet_subset hm hy))))

end Helpers

section Transport

variable {T U : Theory L} [T.Δ₁] [U.Δ₁] {d : V}

/-- **Relativization of internal derivations.** Every internal T-derivation
of a sequent `s` yields a U-derivation of `s^δ` together with finitely many
side formulas `¬δ(&i)`, provided U proves (with such side formulas) the
relativization of every axiom of T, and closed terms are free variables. -/
theorem derivable_relSet (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (relativize L d p) (domSet L d m)))
    {der : V} (h : Derivation T der) :
    ∃ m, Derivable U (relSet L d (fstIdx der) ∪ domSet L d m) := by
  have hdU := hd.isUFormula
  have hFS : ∀ s m, IsFormulaSet L s → IsFormulaSet L (relSet L d s ∪ domSet L d m) :=
    fun s m hs => by simp [isFormulaSet_relSet hd hs, isFormulaSet_domSet hd m]
  apply Derivation.induction1 𝚺
    (P := fun der : V => ∃ m, Derivable U (relSet L d (fstIdx der) ∪ domSet L d m))
    (by definability) h
  -- axL
  · intro s hs p hp hn
    refine ⟨0, ?_⟩
    simp only [fstIdx_axL]
    refine Derivable.em (hFS s 0 hs) (relativize L d p)
      (mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))) ?_
    rw [relativize_neg hdU (hs p hp).isUFormula]
    exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hn))
  -- verum
  · intro s hs hv
    refine ⟨0, ?_⟩
    simp only [fstIdx_verumIntro]
    refine Derivable.verum (hFS s 0 hs) (mem_cup_iff.mpr (Or.inl ?_))
    simpa using relativize_mem_relSet (d := d) hv
  -- and
  · intro s hs p q dp dq hpq hdp hdq ⟨m₁, ih₁⟩ ⟨m₂, ih₂⟩
    rw [hdp.1] at ih₁
    rw [hdq.1] at ih₂
    have hpqF := hs _ hpq
    have hp : IsFormula L p := (IsSemiformula.and.mp hpqF).1
    have hq : IsFormula L q := (IsSemiformula.and.mp hpqF).2
    refine ⟨max m₁ m₂, ?_⟩
    simp only [fstIdx_andIntro]
    have hmem : relativize L d p ^⋏ relativize L d q ∈ relSet L d s ∪ domSet L d (max m₁ m₂) := by
      rw [← relativize_and hp.isUFormula hq.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hpq))
    refine Derivable.and_m hmem ?_ ?_
    · refine Derivable.wk (by simp [hFS s _ hs, isSemiformula_relativize hd hp]) ?_ ih₁
      intro y hy
      rcases mem_cup_iff.mp hy with hy | hy
      · rw [relSet_insert] at hy
        rcases mem_bitInsert_iff.mp hy with rfl | hy
        · simp
        · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hy)))
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
          (Or.inr (domSet_subset (le_max_left m₁ m₂) hy))))
    · refine Derivable.wk (by simp [hFS s _ hs, isSemiformula_relativize hd hq]) ?_ ih₂
      intro y hy
      rcases mem_cup_iff.mp hy with hy | hy
      · rw [relSet_insert] at hy
        rcases mem_bitInsert_iff.mp hy with rfl | hy
        · simp
        · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hy)))
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
          (Or.inr (domSet_subset (le_max_right m₁ m₂) hy))))
  -- or
  · intro s hs p q dp hpq hdp ⟨m, ih⟩
    rw [hdp.1] at ih
    have hpqF := hs _ hpq
    have hp : IsFormula L p := (IsSemiformula.or.mp hpqF).1
    have hq : IsFormula L q := (IsSemiformula.or.mp hpqF).2
    refine ⟨m, ?_⟩
    simp only [fstIdx_orIntro]
    have hmem : relativize L d p ^⋎ relativize L d q ∈ relSet L d s ∪ domSet L d m := by
      rw [← relativize_or hp.isUFormula hq.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hpq))
    refine Derivable.or_m hmem (Derivable.wk (by simp [hFS s _ hs, isSemiformula_relativize hd hp,
      isSemiformula_relativize hd hq]) ?_ ih)
    intro y hy
    rcases mem_cup_iff.mp hy with hy | hy
    · rw [relSet_insert, relSet_insert] at hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      · simp [hy]
    · simp [hy]
  -- all
  · intro s hs p dp hp hdp ⟨m, ih⟩
    rw [hdp.1] at ih
    have hpF : IsSemiformula L 1 p := by simpa using hs _ hp
    refine ⟨m, ?_⟩
    simp only [fstIdx_allIntro]
    have hmem : ^∀ (neg L d ^⋎ relativize L d p) ∈ relSet L d s ∪ domSet L d m := by
      rw [← relativize_all hpF.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))
    refine Derivable.all_m hmem ?_
    rw [free_or (isSemiformula_of_one (n := 0) hd |>.neg |> fun h => by simpa using h)
        (isSemiformula_relativize hd hpF),
      free_neg_domain hd hds, relativize_free hd hds hpF, mem_setShift_union,
      setShift_relSet hd hds hs]
    refine Derivable.or (Derivable.wk ?_ ?_ ih)
    · simp [isFormula_domF hd, isSemiformula_relativize hd hpF.free, isFormulaSet_relSet hd hs.setShift,
        (isFormulaSet_domSet hd m).setShift]
    · intro y hy
      rcases mem_cup_iff.mp hy with hy | hy
      · rw [relSet_insert] at hy
        rcases mem_bitInsert_iff.mp hy with rfl | hy
        · simp
        · simp [hy]
      · rcases mem_bitInsert_iff.mp (domSet_subset_insert_setShift hd hds m hy) with rfl | hy
        · simp
        · simp [hy]
  -- exs
  · intro s hs p t dp hp ht hdp ⟨m, ih⟩
    rw [hdp.1] at ih
    have hpF : IsSemiformula L 1 p := by simpa using hs _ hp
    obtain ⟨j, rfl⟩ := hTerm _ ht
    refine ⟨max m (j + 1), ?_⟩
    simp only [fstIdx_exsIntro]
    have hmem : ^∃ (d ^⋏ relativize L d p) ∈ relSet L d s ∪ domSet L d (max m (j + 1)) := by
      rw [← relativize_exs hpF.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))
    refine Derivable.ex_m hmem ht ?_
    have hsub : substs1 L ^&j (d ^⋏ relativize L d p) =
        substs1 L ^&j d ^⋏ relativize L d (substs1 L ^&j p) := by
      simp only [substs1]
      rw [substs_and hdU (isUFormula_relativize hdU hpF.isUFormula)]
      congr 1
      exact relativize_substs1 hd (show IsSemiterm L 0 (^&j : V) by simp) hpF
    rw [hsub]
    have hFS' := hFS s (max m (j + 1)) hs
    refine Derivable.and ?_ ?_
    · refine Derivable.em (by simp [hFS', hd.substs1 (show IsSemiterm L 0 (^&j : V) by simp)])
        (substs1 L ^&j d) (by simp) ?_
      refine mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr ?_)))
      exact domF_mem_domSet (lt_of_lt_of_le (by simp) (le_max_right m (j + 1)))
    · exact derivable_insert_of_relSet (le_max_left m (j + 1))
        (by simp [hFS', isSemiformula_relativize hd (hpF.substs1 (show IsSemiterm L 0 (^&j : V) by simp))])
        ih
  -- wk
  · intro s hs d' hss hd' ⟨m, ih⟩
    refine ⟨m, ?_⟩
    simp only [fstIdx_wkRule]
    refine Derivable.wk (hFS s m hs) ?_ ih
    intro y hy
    rcases mem_cup_iff.mp hy with hy | hy
    · exact mem_cup_iff.mpr (Or.inl (relSet_subset hss hy))
    · exact mem_cup_iff.mpr (Or.inr hy)
  -- shift
  · intro s hs d' he hd' ⟨m, ih⟩
    refine ⟨m + 1, ?_⟩
    simp only [fstIdx_shiftRule]
    have hs' : IsFormulaSet L (fstIdx d') := hd'.isFormulaSet
    have := Derivable.shift ih
    rw [mem_setShift_union, setShift_relSet hd hds hs', ← he] at this
    refine Derivable.wk (hFS s _ hs) ?_ this
    intro y hy
    rcases mem_cup_iff.mp hy with hy | hy
    · exact mem_cup_iff.mpr (Or.inl hy)
    · exact mem_cup_iff.mpr (Or.inr (setShift_domSet_subset hd hds m hy))
  -- cut
  · intro s hs p d₁ d₂ hd₁ hd₂ ⟨m₁, ih₁⟩ ⟨m₂, ih₂⟩
    rw [hd₁.1] at ih₁
    rw [hd₂.1] at ih₂
    have hp : IsFormula L p := (IsFormulaSet.insert_iff.mp hd₁.isFormulaSet).1
    refine ⟨max m₁ m₂, ?_⟩
    simp only [fstIdx_cutRule]
    have hFS' := hFS s (max m₁ m₂) hs
    refine Derivable.cut (relativize L d p)
      (derivable_insert_of_relSet (le_max_left m₁ m₂)
        (by simp [hFS', isSemiformula_relativize hd hp]) ih₁) ?_
    rw [relativize_neg hdU hp.isUFormula]
    exact derivable_insert_of_relSet (le_max_right m₁ m₂)
      (by simp [hFS', isSemiformula_relativize hd hp.neg]) ih₂
  -- axm
  · intro s hs p hp hT
    obtain ⟨m, hm⟩ := hAx p (hs p hp) hT
    refine ⟨m, ?_⟩
    simp only [fstIdx_axm]
    refine Derivable.wk (hFS s m hs) ?_ hm
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))
    · exact mem_cup_iff.mpr (Or.inr hy)

end Transport

/-! ### Discharging the side formulas -/

section Discharge

variable {U : Theory L} [U.Δ₁] {d : V}

lemma domSet_succ (hd : IsSemiformula L 1 d) (hds : shift L d = d) (m : V) :
    domSet L d (m + 1) = insert (domF L d 0) (setShift L (domSet L d m)) := by
  apply mem_ext; intro y
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simp
    · refine mem_bitInsert_iff.mpr (Or.inr (mem_setShift_iff.mpr ⟨domF L d j, ?_, ?_⟩))
      · exact domF_mem_domSet (by simpa using hi)
      · exact (shift_domF hd hds j).symm
  · intro hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact domF_mem_domSet (by simp)
    · exact setShift_domSet_subset hd hds m hy

/-- One side formula `¬δ(&0)` is discharged: generalize it to `∀x ¬δ(x)` and
cut against `∃x δ(x)`. -/
lemma derivable_of_domSet_succ (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hne : Derivable U (insert (^∃ d) (∅ : V))) {r m : V} (hr : IsFormula L r)
    (hrs : shift L r = r) (h : Derivable U (insert r (domSet L d (m + 1)))) :
    Derivable U (insert r (domSet L d m)) := by
  have hΓ : IsFormulaSet L (insert r (domSet L d m)) := by
    simp [hr, isFormulaSet_domSet hd m]
  -- the derivable sequent is `free (¬d), shift (r, side formulas below m)`
  have h' : Derivable U (insert (free L (neg L d)) (setShift L (insert r (domSet L d m)))) := by
    rw [free_neg_domain hd hds, mem_setShift_insert, hrs]
    refine Derivable.ofSetEq (fun x => ?_) h
    rw [domSet_succ hd hds m]
    simp only [mem_bitInsert_iff]
    tauto
  have hall : Derivable U (insert (^∀ (neg L d)) (insert r (domSet L d m))) :=
    Derivable.all hd.neg h'
  have hex : Derivable U (insert (^∃ d) (insert r (domSet L d m))) := by
    refine Derivable.wk (by simp [hd, hΓ]) ?_ hne
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · simp at hy
  refine Derivable.cut (^∀ (neg L d)) hall ?_
  rw [neg_all hd.isUFormula.neg, hd.isUFormula.neg_neg]
  exact hex

/-- All side formulas are discharged, by internal induction on their number. -/
lemma derivable_of_domSet (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hne : Derivable U (insert (^∃ d) (∅ : V))) {r : V} (hr : IsFormula L r)
    (hrs : shift L r = r) (m : V) (h : Derivable U (insert r (domSet L d m))) :
    Derivable U (insert r (∅ : V)) := by
  have key : ∀ k ≤ m, ∃ j, j + k = m ∧ Derivable U (insert r (domSet L d j)) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · definability
    · intro _; exact ⟨m, by simp, h⟩
    · case succ k ih =>
      intro hk
      obtain ⟨j, hj, hder⟩ := ih (le_trans (by simp) hk)
      rcases zero_or_succ j with (rfl | ⟨j', rfl⟩)
      · exfalso
        simp [← hj] at hk
      · refine ⟨j', ?_, derivable_of_domSet_succ hd hds hne hr hrs hder⟩
        rw [← hj, add_comm k 1, ← add_assoc]
  obtain ⟨j, hj, hder⟩ := key m le_rfl
  have hj0 : j = 0 := by simpa using hj
  have hempty : domSet L d (0 : V) = ∅ := mem_ext fun y => by simp [mem_domSet_iff]
  rw [hj0, hempty] at hder
  exact hder

end Discharge

/-! ### The interpretation theorem -/

section Interpretation

variable {T U : Theory L} [T.Δ₁] [U.Δ₁] {d : V}

/-- **Internal relative interpretation.** In every IΣ₁ model: if U proves
`∃x δ(x)` and the relativization of every axiom of T (with domain side
formulas), then U proves the relativization of every shift-fixed theorem of
T. -/
theorem provable_relativize (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (relativize L d p) (domSet L d m)))
    (hne : Provable U (^∃ d)) {φ : V} (hφ : Provable T φ) (hφs : shift L φ = φ) :
    Provable U (relativize L d φ) := by
  obtain ⟨der, hder⟩ := hφ.toDerivable
  have hφF : IsFormula L φ := by
    have := hder.2.isFormulaSet
    rw [hder.1] at this
    simpa using this
  obtain ⟨m, hm⟩ := derivable_relSet hd hds hTerm hAx hder.2
  rw [hder.1, relSet_insert] at hm
  have hrelempty : relSet L d (∅ : V) = ∅ := mem_ext fun y => by simp [mem_relSet_iff]
  rw [hrelempty] at hm
  have hm' : Derivable U (insert (relativize L d φ) (domSet L d m)) := by
    refine Derivable.ofSetEq (fun x => ?_) hm
    simp
  apply Derivable.toProvable
  exact derivable_of_domSet hd hds hne.toDerivable (isSemiformula_relativize hd hφF)
    (by rw [relativize_shift hd hds hφF.isUFormula, hφs]) m hm'

/-- **Consistency transfer**: a T-refutation yields a U-refutation. -/
theorem provable_falsum_of_relativize (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (relativize L d p) (domSet L d m)))
    (hne : Provable U (^∃ d)) (h : Provable T (^⊥ : V)) : Provable U (^⊥ : V) := by
  simpa using provable_relativize hd hds hTerm hAx hne h (by simp)

end Interpretation

end LeanProofs.BoundedPAConsistency.InternalRelativization
