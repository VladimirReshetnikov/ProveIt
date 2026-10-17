import ZFCinPA.LStepBasic

set_option autoImplicit false
noncomputable section

/-!
# The atomic steps of the reflection generator

`EnvTransform.atomCode R a b` reads environment slots `a` and `b` through the
numeral formulas `numChainCode a`, `numChainCode b`. Over the six-placeholder
language the numeral formulas are the placeholders `P₀`, `P₂`, and the atom
body is built literally from the same fixed pieces (`memAtomBody`,
`eqAtomBody`), so that its translation is the transform's code.

`memAtomTemplate`: if `P₀` and `P₂` each define a unique natural number
(`numOK`), `P₄` is the membership atom read at those slots and `F₅` is the
successor, then `F₅` is a total reflection function for `P₄`, with code
`⟨0, ⟨a, b⟩⟩` (`satIn_memAtom`). `eqAtomTemplate` is the same for equality
(code `⟨1, ⟨a, b⟩⟩`, `satIn_eqAtom`).
-/

namespace LeanProofs.ZFCinPA.LStepAtom

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepBasic

/-- `m ∈ ω`. -/
def natP : SetTheorySemisentence 1 :=
  piece 0 (.atom (BoundedZFCConsistency.fNatF 0) (SetTheory.BusyBeaver.ZFC.ConstructibleDef.argsOf [0]))

section Semantics

open SetTheory.BusyBeaver.ZFC.NamedZF SetTheory.BusyBeaver.ZFC.InternalOrd
  SetTheory.BusyBeaver.ZFC.InternalRank SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)
variable (ε : Empty → V)

@[simp] theorem eval_natP (m : V) : natP.Eval ![m] ε ↔ m ∈ _root_.SetTheory.omegaV H := by
  rw [natP, eval_piece]
  simp only [NSat, argsOf, fNatF_spec H]
  simp

@[simp] theorem eval_appXS (m y x t : V) :
    appXS.Eval ![m, y, x, t] ε ↔ _root_.SetTheory.kpair H m x ∈ t := by
  rw [appXS, eval_piece, nsat_pmemF H]
  rfl

@[simp] theorem eval_appYS (m y x t : V) :
    appYS.Eval ![m, y, x, t] ε ↔ _root_.SetTheory.kpair H m y ∈ t := by
  rw [appYS, eval_piece, nsat_pmemF H]
  rfl

omit [SetStructure V] in
@[simp] theorem eval_memXYS [SetStructure V] (y x t : V) :
    memXYS.Eval ![y, x, t] ε ↔ x ∈ y := by
  simp [memXYS]

omit [SetStructure V] in
@[simp] theorem eval_eqXYS [SetStructure V] (y x t : V) :
    eqXYS.Eval ![y, x, t] ε ↔ x = y := by
  simp [eqXYS]

/-- A predicate defines exactly one natural number. -/
def NumOK (N : V → Prop) (n : V) : Prop :=
  (N n ∧ ∀ m, N m → m = n) ∧ n ∈ _root_.SetTheory.omegaV H

include hR in
/-- **The atomic step** (membership and equality). -/
theorem atom_step {Na Nb P : V → Prop} {F : V → V → Prop} {na nb : V}
    (ha : NumOK H Na na) (hb : NumOK H Nb nb)
    (hF : ∀ a g, F a g ↔ g = _root_.SetTheory.vsucc H a) (isEq : Bool)
    (hdefP : ∀ t, P t ↔ ∃ x, (∃ m, Na m ∧ _root_.SetTheory.kpair H m x ∈ t) ∧
      ∃ y, (∃ m, Nb m ∧ _root_.SetTheory.kpair H m y ∈ t) ∧ (if isEq then x = y else x ∈ y)) :
    Tot F ∧ Refl H hP P F := by
  refine tot_refl_congr hF (tot_succ H) ?_
  -- reading the atom at an environment
  have hread : ∀ S t, IsEnvOn H S t → (P t ↔
      if isEq then applyV H t na = applyV H t nb else applyV H t na ∈ applyV H t nb) := by
    intro S t ht
    have hfa := applyV_iff H ht.1 ha.2
    have hfb := applyV_iff H ht.1 hb.2
    rw [hdefP]
    constructor
    · rintro ⟨x, ⟨m, hm, hmx⟩, y, ⟨m', hm', hmy⟩, hxy⟩
      rw [ha.1.2 m hm] at hmx
      rw [hb.1.2 m' hm'] at hmy
      rw [(hfa x).1 hmx, (hfb y).1 hmy]
      exact hxy
    · intro h
      exact ⟨_, ⟨na, ha.1.1, (hfa _).2 rfl⟩, _, ⟨nb, hb.1.1, (hfb _).2 rfl⟩, h⟩
  cases isEq
  · refine ⟨_, isFormCodeSem_memAtom H ha.2 hb.2, fun b hb' _ S hS R hR' a ha' U hU t ht => ?_⟩
    have htS := envOn_stage H hR hP hb' hS ha' hU ht
    rw [hread S t htS, satIn_memAtom H (isSetStructure_stage H hR hP hb' hS hR') ha.2 hb.2 htS]
    simp only [Bool.false_eq_true, if_false]
    rw [hR']
    constructor
    · intro h
      exact ⟨_, _, isEnvOn_apply H htS ha.2, isEnvOn_apply H htS hb.2, h, rfl⟩
    · rintro ⟨x, y, -, -, hxy, hp⟩
      obtain ⟨rfl, rfl⟩ := _root_.SetTheory.kpair_inj H _ _ _ _ hp
      exact hxy
  · refine ⟨_, isFormCodeSem_eqAtom H ha.2 hb.2, fun b hb' _ S hS R hR' a ha' U hU t ht => ?_⟩
    have htS := envOn_stage H hR hP hb' hS ha' hU ht
    rw [hread S t htS, satIn_eqAtom H (isSetStructure_stage H hR hP hb' hS hR') ha.2 hb.2 htS]
    simp

end Semantics

/-! ## The templates -/

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `P₀` defines exactly one natural number. -/
def numOK₀ : Sentence L6 :=
  “(∃ m, !P₀ m ∧ ∀ m', !P₀ m' → m' = m) ∧ ∀ m, !P₀ m → !(lift natP) m”

/-- `P₂` defines exactly one natural number. -/
def numOK₂ : Sentence L6 :=
  “(∃ m, !P₂ m ∧ ∀ m', !P₂ m' → m' = m) ∧ ∀ m, !P₂ m → !(lift natP) m”

/-- The membership atom, read at the slots defined by `P₀` and `P₂`; literally
the shape of `EnvTransform.atomCode`. -/
def memAtomBody : Semisentence L6 1 :=
  ∃⁰ ∃⁰ ((∃⁰ ((P₀ ⇜ ![#0]) ⋏ lift appXS)) ⋏ ((∃⁰ ((P₂ ⇜ ![#0]) ⋏ lift appYS)) ⋏ lift memXYS))

/-- The equality atom, likewise. -/
def eqAtomBody : Semisentence L6 1 :=
  ∃⁰ ∃⁰ ((∃⁰ ((P₀ ⇜ ![#0]) ⋏ lift appXS)) ⋏ ((∃⁰ ((P₂ ⇜ ![#0]) ⋏ lift appYS)) ⋏ lift eqXYS))

def memAtomDefP : Sentence L6 := ∀⁰ ((P₄ 🡘 memAtomBody))
def eqAtomDefP : Sentence L6 := ∀⁰ ((P₄ 🡘 eqAtomBody))

/-- **The membership-atom template.** -/
def memAtomTemplate : Sentence L6 :=
  (numOK₀ ⋏ numOK₂ ⋏ memAtomDefP ⋏ succDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

/-- **The equality-atom template.** -/
def eqAtomTemplate : Sentence L6 :=
  (numOK₀ ⋏ numOK₂ ⋏ eqAtomDefP ⋏ succDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

section Readings

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

theorem models_numOK₀ :
    M↓[L6] ⊧ numOK₀ → ∃ n, NumOK (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (fun m => P₀.Eval ![m] Empty.elim) n := by
  intro h
  simp only [models_iff, numOK₀] at h
  simp [eval_natP (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))] at h
  obtain ⟨⟨n, hn, hu⟩, hω⟩ := h
  exact ⟨n, ⟨hn, hu⟩, hω n hn⟩

theorem models_numOK₂ :
    M↓[L6] ⊧ numOK₂ → ∃ n, NumOK (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (fun m => P₂.Eval ![m] Empty.elim) n := by
  intro h
  simp only [models_iff, numOK₂] at h
  simp [eval_natP (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))] at h
  obtain ⟨⟨n, hn, hu⟩, hω⟩ := h
  exact ⟨n, ⟨hn, hu⟩, hω n hn⟩

theorem models_atomDefP (isEq : Bool)
    (h : M↓[L6] ⊧ (if isEq then eqAtomDefP else memAtomDefP)) :
    ∀ t : M, P₄.Eval ![t] Empty.elim ↔ ∃ x,
      (∃ m, P₀.Eval ![m] Empty.elim ∧
        _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) m x ∈ t) ∧
      ∃ y, (∃ m, P₂.Eval ![m] Empty.elim ∧
        _root_.SetTheory.kpair (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) m y ∈ t) ∧
      (if isEq then x = y else x ∈ y) := by
  cases isEq <;>
  · simp only [Bool.false_eq_true, if_false, if_true, models_iff, memAtomDefP, eqAtomDefP] at h
    simpa [memAtomBody, eqAtomBody,
      eval_appXS (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)),
      eval_appYS (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)),
      Matrix.comp_vecCons', Matrix.constant_eq_singleton] using h

end Readings

theorem atomTemplate_provable (isEq : Bool) :
    templTheory 6 ar6 ⊢ (if isEq then eqAtomTemplate else memAtomTemplate) := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  have key : M↓[L6] ⊧ ((numOK₀ ⋏ numOK₂ ⋏ (if isEq then eqAtomDefP else memAtomDefP) ⋏ succDefF) 🡒
      (totS F₅ ⋏ reflS P₄ F₅)) := by
    simp only [Semantics.Imp.models_imply, Semantics.And.models_and]
    rintro ⟨h₀, h₂, hdefP, hdefF⟩
    obtain ⟨na, hna⟩ := models_numOK₀ h₀
    obtain ⟨nb, hnb⟩ := models_numOK₂ h₂
    rw [models_succDefF] at hdefF
    rw [models_totS, models_reflS]
    exact atom_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (ConstructibleInterpretation.regular_of_modelsZF (V := M))
      (ConstructibleInterpretation.power_of_modelsZF (V := M)) hna hnb hdefF isEq
      (models_atomDefP isEq hdefP)
  cases isEq <;> simpa [eqAtomTemplate, memAtomTemplate] using key

end LeanProofs.ZFCinPA.LStepAtom
