import ZFCinPA.SetRelativization
import BoundedPAConsistency.InternalRelativization

set_option autoImplicit false
noncomputable section

/-!
# Represented interpretations of set theory with defined atoms

`BoundedPAConsistency.InternalRelativization` relativizes internal formulas to
a definable class, leaving atoms unchanged. Interpreting `𝗭𝗙` in the native
CP/GIC theory (`R3` of the plan doc) also reinterprets the atoms: equality by
bisimilarity, membership by membership up to bisimilarity. This module is
the represented counterpart for `ℒₛₑₜ`, with a parameter
`P = ⟪d, ⟪a₌, a∈⟫⟫` packing three internal formula codes:

* `d`, the domain formula `δ(#0)`;
* `a₌` and `a∈`, the meanings of the atoms `#0 = #1` and `#0 ∈ #1`
  (level two, shift-fixed).

The interpretation `interp P p` substitutes the arguments of every atom into
its meaning, negated atoms into the negated meaning, keeps the connectives,
and guards the quantifiers as relativization does:

    R(t, u) ↦ a_R(t, u),   ∀ q ↦ ∀ (¬δ(#0) ∨ q^I),   ∃ q ↦ ∃ (δ(#0) ∧ q^I).

It is one `UformulaRec1` construction, total and `Σ₁` in every model of
`IΣ₁`. The domain side formulas and their discharge are reused from
`InternalRelativization` (they depend only on `d`). The main results are the
commutation laws (negation, shift, substitution, `free`), the transport of
internal derivations `derivable_iSet`, and `provable_falsum_of_interp`:
`Prov_T(⊥) → Prov_U(⊥)` when `U` proves `∃x δ(x)` and the interpretation of
every `T`-axiom.
-/

namespace LeanProofs.ZFCinPA.InternalInterpretation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.InternalRelativization
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Internal set-language relation symbols are binary equality or membership. -/
private theorem isRel_set {k R : V} (hR : (ℒₛₑₜ).IsRel k R) : k = 2 ∧ (R = 0 ∨ R = 1) :=
  LeanProofs.ZFCinPA.SetRelativization.set_isRel hR

/-- The domain component of the parameter. -/
abbrev dom (P : V) : V := π₁ P

/-- The meaning of the atom with relation code `R` (`0` is equality). -/
noncomputable def atomOf (P R : V) : V := if R = 0 then π₁ (π₂ P) else π₂ (π₂ P)

/-- The graph of `atomOf`. -/
noncomputable def atomOfDef : 𝚺₁.Semisentence 3 := .mkSigma
  “a P R. (R = 0 ∧ ∃ p2, !pi₂Def p2 P ∧ !pi₁Def a p2) ∨ (R ≠ 0 ∧ ∃ p2, !pi₂Def p2 P ∧ !pi₂Def a p2)”

instance atomOf.defined : 𝚺₁-Function₂ (atomOf : V → V → V) via atomOfDef := .mk fun v ↦ by
  unfold atomOf
  by_cases h : v 2 = 0 <;> simp [atomOfDef, h]

namespace Interpretation

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ a, !atomOfDef a param R ∧
    !(substsGraph ℒₛₑₜ) y v a”
  nrel := .mkSigma “y param k R v. ∃ a, !atomOfDef a param R ∧
    ∃ z, !(substsGraph ℒₛₑₜ) z v a ∧ !(negGraph ℒₛₑₜ) y z”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. ∃ d, !pi₁Def d param ∧ ∃ nd, !(negGraph ℒₛₑₜ) nd d ∧
    ∃ z, !qqOrDef z nd y₁ ∧ !qqAllDef y z”
  exs := .mkSigma “y param p₁ y₁. ∃ d, !pi₁Def d param ∧ ∃ z, !qqAndDef z d y₁ ∧ !qqExsDef y z”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel := fun P _ R v ↦ subst ℒₛₑₜ v (atomOf P R)
  nrel := fun P _ R v ↦ neg ℒₛₑₜ (subst ℒₛₑₜ v (atomOf P R))
  verum := fun _ ↦ ^⊤
  falsum := fun _ ↦ ^⊥
  and := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all := fun P _ y₁ ↦ ^∀ (neg ℒₛₑₜ (π₁ P) ^⋎ y₁)
  exs := fun P _ y₁ ↦ ^∃ ((π₁ P) ^⋏ y₁)
  allChanges := fun P ↦ P
  exsChanges := fun P ↦ P
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

end Interpretation

open Interpretation

/-- The interpretation of the internal formula `p` under the parameter `P`. -/
noncomputable def interp (P p : V) : V := construction.result ℒₛₑₜ P p

noncomputable def interpGraph : 𝚺₁.Semisentence 3 := blueprint.result ℒₛₑₜ

instance interp.defined : 𝚺₁-Function₂[V] interp via interpGraph := construction.result_defined

instance interp.definable : 𝚺₁-Function₂[V] interp := interp.defined.to_definable

section Equations

variable {P : V}

@[simp] lemma interp_rel {k R v : V} (hR : (ℒₛₑₜ).IsRel k R) (hv : IsUTermVec ℒₛₑₜ k v) :
    interp P (^rel k R v) = subst ℒₛₑₜ v (atomOf P R) := by
  simp [interp, hR, hv, construction]

@[simp] lemma interp_nrel {k R v : V} (hR : (ℒₛₑₜ).IsRel k R) (hv : IsUTermVec ℒₛₑₜ k v) :
    interp P (^nrel k R v) = neg ℒₛₑₜ (subst ℒₛₑₜ v (atomOf P R)) := by
  simp [interp, hR, hv, construction]

@[simp] lemma interp_verum : interp P (^⊤ : V) = ^⊤ := by simp [interp, construction]

@[simp] lemma interp_falsum : interp P (^⊥ : V) = ^⊥ := by simp [interp, construction]

@[simp] lemma interp_and {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    interp P (p ^⋏ q) = interp P p ^⋏ interp P q := by
  simp [interp, hp, hq, construction]

@[simp] lemma interp_or {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    interp P (p ^⋎ q) = interp P p ^⋎ interp P q := by
  simp [interp, hp, hq, construction]

@[simp] lemma interp_all {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    interp P (^∀ p) = ^∀ (neg ℒₛₑₜ (dom P) ^⋎ interp P p) := by
  simp [interp, hp, construction]

@[simp] lemma interp_exs {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    interp P (^∃ p) = ^∃ (dom P ^⋏ interp P p) := by
  simp [interp, hp, construction]

end Equations

/-- The parameter is well-formed: a shift-fixed one-variable domain formula and
shift-fixed two-variable atom meanings. -/
structure Good (P : V) : Prop where
  isDom : IsSemiformula ℒₛₑₜ 1 (dom P)
  domShift : shift ℒₛₑₜ (dom P) = dom P
  isAtom : ∀ R, IsSemiformula ℒₛₑₜ 2 (atomOf P R)
  atomShift : ∀ R, shift ℒₛₑₜ (atomOf P R) = atomOf P R

section Laws

variable {P : V}

lemma isSemiformula_interp (hP : Good P) {n p : V} :
    IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n (interp P p) := by
  apply IsSemiformula.sigma1_structural_induction
  · definability
  · intro n k R v hR hv
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_rel hR hv.isUTerm]
    exact (hP.isAtom R).subst hv
  · intro n k R v hR hv
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_nrel hR hv.isUTerm]
    exact ((hP.isAtom R).subst hv).neg
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp.isUFormula, ihp, isSemiformula_of_one hP.isDom]
  · intro n p hp ihp; simp [hp.isUFormula, ihp, isSemiformula_of_one hP.isDom]

/-- Interpretation commutes with negation. -/
lemma interp_neg (hP : Good P) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    neg ℒₛₑₜ (interp P p) = interp P (neg ℒₛₑₜ p) := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun n p ↦ neg ℒₛₑₜ (interp P p) = interp P (neg ℒₛₑₜ p)) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv
    rw [interp_rel hR hv.isUTerm, neg_rel hR hv.isUTerm, interp_nrel hR hv.isUTerm]
  · intro n k R v hR hv
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_nrel hR hv.isUTerm, neg_nrel hR hv.isUTerm, interp_rel hR hv.isUTerm,
      ((hP.isAtom R).subst hv).isUFormula.neg_neg]
  · simp
  · simp
  · intro n p q hp hq ihp ihq
    have hip := isSemiformula_interp hP hp
    have hiq := isSemiformula_interp hP hq
    simp [hp.isUFormula, hq.isUFormula, hip.isUFormula, hiq.isUFormula, hp.isUFormula.neg,
      hq.isUFormula.neg, ihp, ihq]
  · intro n p q hp hq ihp ihq
    have hip := isSemiformula_interp hP hp
    have hiq := isSemiformula_interp hP hq
    simp [hp.isUFormula, hq.isUFormula, hip.isUFormula, hiq.isUFormula, hp.isUFormula.neg,
      hq.isUFormula.neg, ihp, ihq]
  · intro n p hp ihp
    have hip := isSemiformula_interp hP hp
    simp [hp.isUFormula, hip.isUFormula, hp.isUFormula.neg, hP.isDom.isUFormula,
      hP.isDom.isUFormula.neg, ihp]
  · intro n p hp ihp
    have hip := isSemiformula_interp hP hp
    simp [hp.isUFormula, hip.isUFormula, hp.isUFormula.neg, hP.isDom.isUFormula, ihp]

/-- Interpretation commutes with the shift of free variables. -/
lemma interp_shift (hP : Good P) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    shift ℒₛₑₜ (interp P p) = interp P (shift ℒₛₑₜ p) := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun n p ↦ shift ℒₛₑₜ (interp P p) = interp P (shift ℒₛₑₜ p)) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_rel hR hv.isUTerm, shift_substs (hP.isAtom R) hv, hP.atomShift R,
      shift_rel hR hv.isUTerm, interp_rel hR hv.isUTerm.termShiftVec]
  · intro n k R v hR hv
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_nrel hR hv.isUTerm, shift_neg ((hP.isAtom R).subst hv), shift_substs (hP.isAtom R) hv,
      hP.atomShift R, shift_nrel hR hv.isUTerm, interp_nrel hR hv.isUTerm.termShiftVec]
  · simp
  · simp
  · intro n p q hp hq ihp ihq
    have hip := isSemiformula_interp hP hp
    have hiq := isSemiformula_interp hP hq
    simp [hp.isUFormula, hq.isUFormula, hip.isUFormula, hiq.isUFormula, hp.isUFormula.shift,
      hq.isUFormula.shift, ihp, ihq]
  · intro n p q hp hq ihp ihq
    have hip := isSemiformula_interp hP hp
    have hiq := isSemiformula_interp hP hq
    simp [hp.isUFormula, hq.isUFormula, hip.isUFormula, hiq.isUFormula, hp.isUFormula.shift,
      hq.isUFormula.shift, ihp, ihq]
  · intro n p hp ihp
    have hip := isSemiformula_interp hP hp
    simp [hp.isUFormula, hip.isUFormula, hp.isUFormula.shift, hP.isDom.isUFormula.neg, ihp,
      shift_neg hP.isDom, hP.domShift]
  · intro n p hp ihp
    have hip := isSemiformula_interp hP hp
    simp [hp.isUFormula, hip.isUFormula, hp.isUFormula.shift, hP.isDom.isUFormula, ihp, hP.domShift]

end Laws

section Subst

variable {P : V}

/-- Interpretation commutes with substitution of terms for bound variables. -/
lemma interp_subst (hP : Good P) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    ∀ {a w : V}, IsSemitermVec ℒₛₑₜ n a w →
      subst ℒₛₑₜ w (interp P p) = interp P (subst ℒₛₑₜ w p) := by
  suffices h : ∀ a w : V, IsSemitermVec ℒₛₑₜ n a w →
      subst ℒₛₑₜ w (interp P p) = interp P (subst ℒₛₑₜ w p) from fun {a w} hw => h a w hw
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv a w hw
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_rel hR hv.isUTerm, substs_substs (hP.isAtom R) hw hv, substs_rel hR hv.isUTerm,
      interp_rel hR (hw.termSubstVec hv).isUTerm]
  · intro n k R v hR hv a w hw
    obtain ⟨rfl, -⟩ := isRel_set hR
    rw [interp_nrel hR hv.isUTerm, substs_neg ((hP.isAtom R).subst hv) hw,
      substs_substs (hP.isAtom R) hw hv, substs_nrel hR hv.isUTerm,
      interp_nrel hR (hw.termSubstVec hv).isUTerm]
  · intro n a w _; simp
  · intro n a w _; simp
  · intro n p q hp hq ihp ihq a w hw
    rw [interp_and hp.isUFormula hq.isUFormula,
      substs_and (isSemiformula_interp hP hp).isUFormula (isSemiformula_interp hP hq).isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      interp_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula, ihp a w hw, ihq a w hw]
  · intro n p q hp hq ihp ihq a w hw
    rw [interp_or hp.isUFormula hq.isUFormula,
      substs_or (isSemiformula_interp hP hp).isUFormula (isSemiformula_interp hP hq).isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      interp_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula, ihp a w hw, ihq a w hw]
  · intro n p hp ih a w hw
    have hd' : IsSemiformula ℒₛₑₜ (n + 1) (dom P) := isSemiformula_of_one hP.isDom
    rw [interp_all hp.isUFormula,
      substs_all (by simp [hP.isDom.isUFormula, (isSemiformula_interp hP hp).isUFormula]),
      substs_or hP.isDom.isUFormula.neg (isSemiformula_interp hP hp).isUFormula,
      substs_neg hd' hw.qVec, subst_qVec_domain hP.isDom hw,
      substs_all hp.isUFormula, interp_all (hp.subst hw.qVec).isUFormula,
      ih (a + 1) (qVec ℒₛₑₜ w) hw.qVec]
  · intro n p hp ih a w hw
    rw [interp_exs hp.isUFormula,
      substs_ex (by simp [hP.isDom.isUFormula, (isSemiformula_interp hP hp).isUFormula]),
      substs_and hP.isDom.isUFormula (isSemiformula_interp hP hp).isUFormula,
      subst_qVec_domain hP.isDom hw,
      substs_ex hp.isUFormula, interp_exs (hp.subst hw.qVec).isUFormula,
      ih (a + 1) (qVec ℒₛₑₜ w) hw.qVec]

lemma interp_substs1 (hP : Good P) {n t p : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (hp : IsSemiformula ℒₛₑₜ 1 p) :
    substs1 ℒₛₑₜ t (interp P p) = interp P (substs1 ℒₛₑₜ t p) :=
  interp_subst hP hp (show IsSemitermVec ℒₛₑₜ 1 n ?[t] by simp [ht])

lemma interp_free (hP : Good P) {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    free ℒₛₑₜ (interp P p) = interp P (free ℒₛₑₜ p) := by
  simp only [free]
  rw [interp_shift hP hp, interp_substs1 hP (show IsSemiterm ℒₛₑₜ 0 (^&0 : V) by simp) hp.shift]

end Subst

/-! ### Interpreted sequents -/

section Sets

lemma iSet_existsUnique (P s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = interp P x :=
  sigma₁_replacement (by definability) s

/-- The interpreted sequent `s^I`. -/
noncomputable def iSet (P s : V) : V := Classical.choose! (iSet_existsUnique P s)

variable {P : V}

lemma mem_iSet_iff {s y : V} : y ∈ iSet P s ↔ ∃ x ∈ s, y = interp P x :=
  Classical.choose!_spec (iSet_existsUnique P s) y

instance iSet.definable : 𝚺₁-Function₂[V] iSet := by
  apply HierarchySymbol.Definable.of_iff
    (Q := fun v ↦ (∀ y ∈ v 0, ∃ x ∈ v 2, y = interp (v 1) x) ∧
      (∀ x ∈ v 2, interp (v 1) x ∈ v 0))
  · definability
  · intro v
    constructor
    · intro h
      simp only [Fin.isValue] at h
      rw [h]
      exact ⟨fun y hy => mem_iSet_iff.mp hy, fun x hx => mem_iSet_iff.mpr ⟨x, hx, rfl⟩⟩
    · rintro ⟨h₁, h₂⟩
      apply mem_ext; intro y
      constructor
      · intro hy; exact mem_iSet_iff.mpr (h₁ y hy)
      · intro hy
        obtain ⟨x, hx, rfl⟩ := mem_iSet_iff.mp hy
        exact h₂ x hx

lemma iSet_insert {x s : V} : iSet P (insert x s) = insert (interp P x) (iSet P s) :=
  mem_ext fun y => by simp [mem_iSet_iff]

lemma iSet_subset {s s' : V} (h : s ⊆ s') : iSet P s ⊆ iSet P s' := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_iSet_iff.mp hy
  exact mem_iSet_iff.mpr ⟨x, h hx, rfl⟩

lemma interp_mem_iSet {x s : V} (h : x ∈ s) : interp P x ∈ iSet P s :=
  mem_iSet_iff.mpr ⟨x, h, rfl⟩

lemma isFormulaSet_iSet (hP : Good P) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    IsFormulaSet ℒₛₑₜ (iSet P s) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_iSet_iff.mp hy
  exact isSemiformula_interp hP (hs x hx)

lemma setShift_iSet (hP : Good P) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    setShift ℒₛₑₜ (iSet P s) = iSet P (setShift ℒₛₑₜ s) :=
  mem_ext fun y => by
    simp only [mem_setShift_iff, mem_iSet_iff]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨shift ℒₛₑₜ x, ⟨x, hx, rfl⟩, interp_shift hP (hs x hx)⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨interp P x, ⟨x, hx, rfl⟩, (interp_shift hP (hs x hx)).symm⟩

lemma derivable_insert_of_iSet {U : FirstOrder.Theory ℒₛₑₜ} [U.Δ₁] {x s m m' : V} (hm : m ≤ m')
    (hT : IsFormulaSet ℒₛₑₜ (insert (interp P x) (iSet P s ∪ domSet ℒₛₑₜ (dom P) m')))
    (h : Derivable U (iSet P (insert x s) ∪ domSet ℒₛₑₜ (dom P) m)) :
    Derivable U (insert (interp P x) (iSet P s ∪ domSet ℒₛₑₜ (dom P) m')) := by
  refine Derivable.wk hT ?_ h
  intro y hy
  rcases mem_cup_iff.mp hy with hy | hy
  · rw [iSet_insert] at hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hy)))
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr (domSet_subset hm hy))))

end Sets

section Transport

variable {T U : FirstOrder.Theory ℒₛₑₜ} [T.Δ₁] [U.Δ₁] {P : V}

/-- **Interpretation of internal derivations.** Every internal T-derivation
of a sequent `s` yields a U-derivation of `s^δ` together with finitely many
side formulas `¬δ(&i)`, provided U proves (with such side formulas) the
interpretation of every axiom of T, and closed terms are free variables. -/
theorem derivable_iSet (hP : Good P)
    (hTerm : ∀ t : V, IsTerm ℒₛₑₜ t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    {der : V} (h : Derivation T der) :
    ∃ m, Derivable U (iSet P (fstIdx der) ∪ domSet ℒₛₑₜ (dom P) m) := by
  have hdU := hP.isDom.isUFormula
  have hFS : ∀ s m, IsFormulaSet ℒₛₑₜ s → IsFormulaSet ℒₛₑₜ (iSet P s ∪ domSet ℒₛₑₜ (dom P) m) :=
    fun s m hs => by simp [isFormulaSet_iSet hP hs, isFormulaSet_domSet hP.isDom m]
  apply Derivation.induction1 𝚺
    (P := fun der : V => ∃ m, Derivable U (iSet P (fstIdx der) ∪ domSet ℒₛₑₜ (dom P) m))
    (by definability) h
  -- axL
  · intro s hs p hp hn
    refine ⟨0, ?_⟩
    simp only [fstIdx_axL]
    refine Derivable.em (hFS s 0 hs) (interp P p)
      (mem_cup_iff.mpr (Or.inl (interp_mem_iSet hp))) ?_
    rw [interp_neg hP (hs p hp)]
    exact mem_cup_iff.mpr (Or.inl (interp_mem_iSet hn))
  -- verum
  · intro s hs hv
    refine ⟨0, ?_⟩
    simp only [fstIdx_verumIntro]
    refine Derivable.verum (hFS s 0 hs) (mem_cup_iff.mpr (Or.inl ?_))
    simpa using interp_mem_iSet (P := P) hv
  -- and
  · intro s hs p q dp dq hpq hdp hdq ⟨m₁, ih₁⟩ ⟨m₂, ih₂⟩
    rw [hdp.1] at ih₁
    rw [hdq.1] at ih₂
    have hpqF := hs _ hpq
    have hp : IsFormula ℒₛₑₜ p := (IsSemiformula.and.mp hpqF).1
    have hq : IsFormula ℒₛₑₜ q := (IsSemiformula.and.mp hpqF).2
    refine ⟨max m₁ m₂, ?_⟩
    simp only [fstIdx_andIntro]
    have hmem : interp P p ^⋏ interp P q ∈ iSet P s ∪ domSet ℒₛₑₜ (dom P) (max m₁ m₂) := by
      rw [← interp_and hp.isUFormula hq.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (interp_mem_iSet hpq))
    refine Derivable.and_m hmem ?_ ?_
    · exact derivable_insert_of_iSet (le_max_left m₁ m₂)
        (by simp [hFS s _ hs, isSemiformula_interp hP hp]) ih₁
    · exact derivable_insert_of_iSet (le_max_right m₁ m₂)
        (by simp [hFS s _ hs, isSemiformula_interp hP hq]) ih₂
  -- or
  · intro s hs p q dp hpq hdp ⟨m, ih⟩
    rw [hdp.1] at ih
    have hpqF := hs _ hpq
    have hp : IsFormula ℒₛₑₜ p := (IsSemiformula.or.mp hpqF).1
    have hq : IsFormula ℒₛₑₜ q := (IsSemiformula.or.mp hpqF).2
    refine ⟨m, ?_⟩
    simp only [fstIdx_orIntro]
    have hmem : interp P p ^⋎ interp P q ∈ iSet P s ∪ domSet ℒₛₑₜ (dom P) m := by
      rw [← interp_or hp.isUFormula hq.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (interp_mem_iSet hpq))
    refine Derivable.or_m hmem (Derivable.wk (by simp [hFS s _ hs, isSemiformula_interp hP hp,
      isSemiformula_interp hP hq]) ?_ ih)
    intro y hy
    rcases mem_cup_iff.mp hy with hy | hy
    · rw [iSet_insert, iSet_insert] at hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      · simp [hy]
    · simp [hy]
  -- all
  · intro s hs p dp hp hdp ⟨m, ih⟩
    rw [hdp.1] at ih
    have hpF : IsSemiformula ℒₛₑₜ 1 p := by simpa using hs _ hp
    refine ⟨m, ?_⟩
    simp only [fstIdx_allIntro]
    have hmem : ^∀ (neg ℒₛₑₜ (dom P) ^⋎ interp P p) ∈ iSet P s ∪ domSet ℒₛₑₜ (dom P) m := by
      rw [← interp_all hpF.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (interp_mem_iSet hp))
    refine Derivable.all_m hmem ?_
    rw [free_or (isSemiformula_of_one (n := 0) hP.isDom |>.neg |> fun h => by simpa using h)
        (isSemiformula_interp hP hpF),
      free_neg_domain hP.isDom hP.domShift, interp_free hP hpF, mem_setShift_union,
      setShift_iSet hP hs]
    refine Derivable.or (Derivable.wk ?_ ?_ ih)
    · simp [isFormula_domF hP.isDom, isSemiformula_interp hP hpF.free, isFormulaSet_iSet hP hs.setShift,
        (isFormulaSet_domSet hP.isDom m).setShift]
    · intro y hy
      rcases mem_cup_iff.mp hy with hy | hy
      · rw [iSet_insert] at hy
        rcases mem_bitInsert_iff.mp hy with rfl | hy
        · simp
        · simp [hy]
      · rcases mem_bitInsert_iff.mp (domSet_subset_insert_setShift hP.isDom hP.domShift m hy) with rfl | hy
        · simp
        · simp [hy]
  -- exs
  · intro s hs p t dp hp ht hdp ⟨m, ih⟩
    rw [hdp.1] at ih
    have hpF : IsSemiformula ℒₛₑₜ 1 p := by simpa using hs _ hp
    obtain ⟨j, rfl⟩ := hTerm _ ht
    refine ⟨max m (j + 1), ?_⟩
    simp only [fstIdx_exsIntro]
    have hmem : ^∃ (dom P ^⋏ interp P p) ∈ iSet P s ∪ domSet ℒₛₑₜ (dom P) (max m (j + 1)) := by
      rw [← interp_exs hpF.isUFormula]
      exact mem_cup_iff.mpr (Or.inl (interp_mem_iSet hp))
    refine Derivable.ex_m hmem ht ?_
    have hsub : substs1 ℒₛₑₜ ^&j (dom P ^⋏ interp P p) =
        substs1 ℒₛₑₜ ^&j (dom P) ^⋏ interp P (substs1 ℒₛₑₜ ^&j p) := by
      simp only [substs1]
      rw [substs_and hdU (isSemiformula_interp hP hpF).isUFormula]
      congr 1
      exact interp_substs1 hP (show IsSemiterm ℒₛₑₜ 0 (^&j : V) by simp) hpF
    rw [hsub]
    have hFS' := hFS s (max m (j + 1)) hs
    refine Derivable.and ?_ ?_
    · refine Derivable.em (by simp [hFS', hP.isDom.substs1 (show IsSemiterm ℒₛₑₜ 0 (^&j : V) by simp)])
        (substs1 ℒₛₑₜ ^&j (dom P)) (by simp) ?_
      refine mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr ?_)))
      exact domF_mem_domSet (lt_of_lt_of_le (by simp) (le_max_right m (j + 1)))
    · exact derivable_insert_of_iSet (le_max_left m (j + 1))
        (by simp [hFS', isSemiformula_interp hP (hpF.substs1 (show IsSemiterm ℒₛₑₜ 0 (^&j : V) by simp))])
        ih
  -- wk
  · intro s hs d' hss hd' ⟨m, ih⟩
    refine ⟨m, ?_⟩
    simp only [fstIdx_wkRule]
    refine Derivable.wk (hFS s m hs) ?_ ih
    intro y hy
    rcases mem_cup_iff.mp hy with hy | hy
    · exact mem_cup_iff.mpr (Or.inl (iSet_subset hss hy))
    · exact mem_cup_iff.mpr (Or.inr hy)
  -- shift
  · intro s hs d' he hd' ⟨m, ih⟩
    refine ⟨m + 1, ?_⟩
    simp only [fstIdx_shiftRule]
    have hs' : IsFormulaSet ℒₛₑₜ (fstIdx d') := hd'.isFormulaSet
    have := Derivable.shift ih
    rw [mem_setShift_union, setShift_iSet hP hs', ← he] at this
    refine Derivable.wk (hFS s _ hs) ?_ this
    intro y hy
    rcases mem_cup_iff.mp hy with hy | hy
    · exact mem_cup_iff.mpr (Or.inl hy)
    · exact mem_cup_iff.mpr (Or.inr (setShift_domSet_subset hP.isDom hP.domShift m hy))
  -- cut
  · intro s hs p d₁ d₂ hd₁ hd₂ ⟨m₁, ih₁⟩ ⟨m₂, ih₂⟩
    rw [hd₁.1] at ih₁
    rw [hd₂.1] at ih₂
    have hp : IsFormula ℒₛₑₜ p := (IsFormulaSet.insert_iff.mp hd₁.isFormulaSet).1
    refine ⟨max m₁ m₂, ?_⟩
    simp only [fstIdx_cutRule]
    have hFS' := hFS s (max m₁ m₂) hs
    refine Derivable.cut (interp P p)
      (derivable_insert_of_iSet (le_max_left m₁ m₂)
        (by simp [hFS', isSemiformula_interp hP hp]) ih₁) ?_
    rw [interp_neg hP hp]
    exact derivable_insert_of_iSet (le_max_right m₁ m₂)
      (by simp [hFS', isSemiformula_interp hP hp.neg]) ih₂
  -- axm
  · intro s hs p hp hT
    obtain ⟨m, hm⟩ := hAx p (hs p hp) hT
    refine ⟨m, ?_⟩
    simp only [fstIdx_axm]
    refine Derivable.wk (hFS s m hs) ?_ hm
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact mem_cup_iff.mpr (Or.inl (interp_mem_iSet hp))
    · exact mem_cup_iff.mpr (Or.inr hy)

lemma derivable_interp_of_provable (hP : Good P)
    (hTerm : ∀ t : V, IsTerm ℒₛₑₜ t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    {φ : V} (h : Provable T φ) :
    ∃ m, Derivable U (insert (interp P φ) (domSet ℒₛₑₜ (dom P) m)) := by
  obtain ⟨der, hder⟩ := h.toDerivable
  obtain ⟨m, hm⟩ := derivable_iSet hP hTerm hAx hder.2
  rw [hder.1, iSet_insert] at hm
  have hrelempty : iSet P (∅ : V) = ∅ := mem_ext fun y => by simp [mem_iSet_iff]
  rw [hrelempty] at hm
  exact ⟨m, Derivable.ofSetEq (fun x => by simp) hm⟩

lemma derivable_domSet_mono {δ x m m' : V} (hδ : IsSemiformula ℒₛₑₜ 1 δ)
    (hm : m ≤ m') (hx : IsFormula ℒₛₑₜ x)
    (h : Derivable U (insert x (domSet ℒₛₑₜ δ m))) :
    Derivable U (insert x (domSet ℒₛₑₜ δ m')) := by
  refine Derivable.wk (by simp [hx, isFormulaSet_domSet hδ m']) ?_ h
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · exact mem_bitInsert_iff.mpr (Or.inr (domSet_subset hm hy))

end Transport

section Interpretation

variable {T U : FirstOrder.Theory ℒₛₑₜ} [T.Δ₁] [U.Δ₁] {P : V}

/-- **Internal relative interpretation.** In every IΣ₁ model: if U proves
`∃x δ(x)` and the interpretation of every axiom of T (with domain side
formulas), then U proves the interpretation of every shift-fixed theorem of
T. -/
theorem provable_interp (hP : Good P)
    (hTerm : ∀ t : V, IsTerm ℒₛₑₜ t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    (hne : Provable U (^∃ (dom P))) {φ : V} (hφ : Provable T φ) (hφs : shift ℒₛₑₜ φ = φ) :
    Provable U (interp P φ) := by
  obtain ⟨der, hder⟩ := hφ.toDerivable
  have hφF : IsFormula ℒₛₑₜ φ := by
    have := hder.2.isFormulaSet
    rw [hder.1] at this
    simpa using this
  obtain ⟨m, hm'⟩ := derivable_interp_of_provable hP hTerm hAx hφ
  apply Derivable.toProvable
  exact derivable_of_domSet hP.isDom hP.domShift hne.toDerivable (isSemiformula_interp hP hφF)
    (by rw [interp_shift hP hφF, hφs]) m hm'

/-- **Consistency transfer**: a T-refutation yields a U-refutation. -/
theorem provable_falsum_of_interp (hP : Good P)
    (hTerm : ∀ t : V, IsTerm ℒₛₑₜ t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    (hne : Provable U (^∃ (dom P))) (h : Provable T (^⊥ : V)) : Provable U (^⊥ : V) := by
  simpa using provable_interp hP hTerm hAx hne h (by simp)

end Interpretation

end LeanProofs.ZFCinPA.InternalInterpretation
