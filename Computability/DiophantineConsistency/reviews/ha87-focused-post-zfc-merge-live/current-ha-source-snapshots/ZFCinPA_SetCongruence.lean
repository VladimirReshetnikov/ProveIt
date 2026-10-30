import ZFCinPA.SetPlaceholderQuotient
import Foundation.Meta.ClProver
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory

/-!
# Internal equality replacement for model-coded `ℒₛₑₜ` formulas

The equality-quotient module (`ZFCinPA.SetPlaceholderQuotient`) proves
source sentences of the form `congruence 🡒 σ`.  To reach `σ` itself, the
compiled internal proof needs the congruence antecedent discharged *inside*
the internalized theory, at a placeholder interpretation whose Gödel code
may be a nonstandard element of `V`.  Since equality replacement is a
schema over internal syntax, this requires `𝚺₁` structural induction on the
coded formula — the `ℒₛₑₜ` counterpart of Foundation's
`Bootstrapping.Arithmetic.replace` (`EquationalTheory`), which is stated
for `ℒₒᵣ` only.

This module ports that development to `ℒₛₑₜ`, for an arbitrary `Δ₁` set
theory containing the equality axioms (in practice `𝗭𝗙𝗖`):

* internal recognition of the `ℒₛₑₜ` symbol codes (`isFunc_iff_Set`,
  `isRel_iff_Set`) — the language is function-free, so the term layer of
  the induction degenerates to variables;
* typed internal atoms `eqAtom`/`neAtom`/`memAtom`/`nmemAtom`;
* seed laws (`set_eq_refl`, `subst_eq`, `subst_mem`, …) obtained by outer
  completeness over set structures and Hilbert–Bernays **D1**;
* `setReplace : T.internalize V ⊢ (u₁ ≐ₛ u₂) 🡒 φ.subst ![u₁] 🡒 φ.subst ![u₂]`
  for every model-coded `φ : Bootstrapping.Semiformula V ℒₛₑₜ 1`.

The parameter firewall of `ZFCinPA.LevelCodeTower` is respected: the only
concrete symbol codes manipulated are the two relation codes of `ℒₛₑₜ`
(`0` and `1`); formula codes stay symbolic throughout.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetCongruence

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LO.Entailment LO.Entailment.FiniteContext
open LeanProofs.ZFCinPA

/-! ## Internal recognition of the `ℒₛₑₜ` symbols

`ℒₛₑₜ` has no function symbols, and exactly two relation symbols, both
binary, coded `0` (`=`) and `1` (`∈`).  These lemmas mirror Foundation's
`isFunc_iff_LOR`/`isRel_iff_LOR`. -/

/-- The `ℕ`-code of the equality symbol of `ℒₛₑₜ`. -/
def setEqIndex : ℕ := Encodable.encode (Language.Set.Rel.eq : (ℒₛₑₜ).Rel 2)

/-- The `ℕ`-code of the membership symbol of `ℒₛₑₜ`. -/
def setMemIndex : ℕ := Encodable.encode (Language.Set.Rel.mem : (ℒₛₑₜ).Rel 2)

lemma setEqIndex_eq_zero : setEqIndex = 0 := rfl

lemma setMemIndex_eq_one : setMemIndex = 1 := rfl

section symbols

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma func_def_Set :
    (ℒₛₑₜ).isFunc = .mkSigma “k f. ⊥” := rfl

lemma rel_def_Set :
    (ℒₛₑₜ).isRel =
      .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” := rfl

lemma coe_setEqIndex_eq : ((setEqIndex : ℕ) : V) = 0 := by
  rw [setEqIndex_eq_zero]; simp

lemma coe_setMemIndex_eq : ((setMemIndex : ℕ) : V) = 1 := by
  rw [setMemIndex_eq_one]; simp

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- No element of `V` codes a function symbol of `ℒₛₑₜ`. -/
@[simp] lemma isFunc_iff_Set {k f : V} : ¬(ℒₛₑₜ).IsFunc k f := by
  rw [isFunc_def (L := ℒₛₑₜ), func_def_Set]
  simp

/-- The internal relation symbols of `ℒₛₑₜ` are the codes of `=` and `∈`. -/
lemma isRel_iff_Set {k R : V} :
    (ℒₛₑₜ).IsRel k R ↔
    (k = 2 ∧ R = ((setEqIndex : ℕ) : V)) ∨
    (k = 2 ∧ R = ((setMemIndex : ℕ) : V)) := by
  rw [isRel_def (L := ℒₛₑₜ), rel_def_Set, coe_setEqIndex_eq, coe_setMemIndex_eq]
  simp

end symbols

/-! ## Typed internal atoms -/

section atoms

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n : ℕ}

/-- The typed internal equality atom of `ℒₛₑₜ`. -/
noncomputable def eqAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.rel Language.Set.Rel.eq ![t, u]

/-- The typed internal disequality atom of `ℒₛₑₜ`. -/
noncomputable def neAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.nrel Language.Set.Rel.eq ![t, u]

/-- The typed internal membership atom of `ℒₛₑₜ`. -/
noncomputable def memAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.rel Language.Set.Rel.mem ![t, u]

/-- The typed internal non-membership atom of `ℒₛₑₜ`. -/
noncomputable def nmemAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.nrel Language.Set.Rel.mem ![t, u]

end atoms

local infix:46 " ≐ₛ " => eqAtom
local infix:46 " ≉ₛ " => neAtom
local infix:46 " ∊ₛ " => memAtom
local infix:46 " ∉ₛ " => nmemAtom

section atomLemmas

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n m : ℕ}

@[simp] lemma eqAtom_neg (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    ∼(t ≐ₛ u) = (t ≉ₛ u) := by
  simp [eqAtom, neAtom]

@[simp] lemma neAtom_neg (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    ∼(t ≉ₛ u) = (t ≐ₛ u) := by
  simp [eqAtom, neAtom]

@[simp] lemma memAtom_neg (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    ∼(t ∊ₛ u) = (t ∉ₛ u) := by
  simp [memAtom, nmemAtom]

@[simp] lemma nmemAtom_neg (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    ∼(t ∉ₛ u) = (t ∊ₛ u) := by
  simp [memAtom, nmemAtom]

@[simp] lemma eqAtom_shift (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ≐ₛ u).shift = (t.shift ≐ₛ u.shift) := by
  simp [eqAtom]

@[simp] lemma neAtom_shift (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ≉ₛ u).shift = (t.shift ≉ₛ u.shift) := by
  simp [neAtom]

@[simp] lemma memAtom_shift (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ∊ₛ u).shift = (t.shift ∊ₛ u.shift) := by
  simp [memAtom]

@[simp] lemma nmemAtom_shift (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ∉ₛ u).shift = (t.shift ∉ₛ u.shift) := by
  simp [nmemAtom]

@[simp] lemma eqAtom_subst (w : Bootstrapping.SemitermVec V ℒₛₑₜ n m)
    (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ≐ₛ u).subst w = (t.subst w ≐ₛ u.subst w) := by
  simp [eqAtom]

@[simp] lemma neAtom_subst (w : Bootstrapping.SemitermVec V ℒₛₑₜ n m)
    (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ≉ₛ u).subst w = (t.subst w ≉ₛ u.subst w) := by
  simp [neAtom]

@[simp] lemma memAtom_subst (w : Bootstrapping.SemitermVec V ℒₛₑₜ n m)
    (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ∊ₛ u).subst w = (t.subst w ∊ₛ u.subst w) := by
  simp [memAtom]

@[simp] lemma nmemAtom_subst (w : Bootstrapping.SemitermVec V ℒₛₑₜ n m)
    (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ∉ₛ u).subst w = (t.subst w ∉ₛ u.subst w) := by
  simp [nmemAtom]

@[simp] lemma val_eqAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ≐ₛ u).val =
      ^rel 2 ((setEqIndex : ℕ) : V) ?[t.val, u.val] := by
  simp [eqAtom, Bootstrapping.Semiformula.rel]
  rfl

@[simp] lemma val_neAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ≉ₛ u).val =
      ^nrel 2 ((setEqIndex : ℕ) : V) ?[t.val, u.val] := by
  simp [neAtom, Bootstrapping.Semiformula.nrel]
  rfl

@[simp] lemma val_memAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ∊ₛ u).val =
      ^rel 2 ((setMemIndex : ℕ) : V) ?[t.val, u.val] := by
  simp [memAtom, Bootstrapping.Semiformula.rel]
  rfl

@[simp] lemma val_nmemAtom (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    (t ∉ₛ u).val =
      ^nrel 2 ((setMemIndex : ℕ) : V) ?[t.val, u.val] := by
  simp [nmemAtom, Bootstrapping.Semiformula.nrel]
  rfl

end atomLemmas

/-! ## Evaluation of the standard atoms in set structures -/

section standard

@[simp] lemma standard_rel_eq {M : Type*} [SetStructure M] (v : Fin 2 → M) :
    Structure.rel (L := ℒₛₑₜ) (M := M) Language.Set.Rel.eq v ↔ v 0 = v 1 :=
  Iff.rfl

@[simp] lemma standard_rel_mem {M : Type*} [SetStructure M] (v : Fin 2 → M) :
    Structure.rel (L := ℒₛₑₜ) (M := M) Language.Set.Rel.mem v ↔ v 0 ∈ v 1 :=
  Iff.rfl

end standard

/-! ## Seed laws by outer completeness and D1 -/

section main

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)
local postfix:max "⇞" => Bootstrapping.Semiterm.shift
local postfix:max "⤉" => Bootstrapping.Semiformula.shift

/-- The source equality atom, at the syntactic level. -/
def sEq {ξ : Type*} {n : ℕ} (t u : Semiterm ℒₛₑₜ ξ n) :
    Semiformula ℒₛₑₜ ξ n :=
  Semiformula.rel Language.Set.Rel.eq ![t, u]

/-- The source membership atom, at the syntactic level. -/
def sMem {ξ : Type*} {n : ℕ} (t u : Semiterm ℒₛₑₜ ξ n) :
    Semiformula ℒₛₑₜ ξ n :=
  Semiformula.rel Language.Set.Rel.mem ![t, u]

/-- Typed quotation of a binary-vector term tuple, in the pointwise form
produced by `typed_quote_rel`.  Not a global `simp` lemma (lambda head);
passed explicitly where needed. -/
lemma quote_vec2_eta {n : ℕ} (t u : SyntacticSemiterm ℒₛₑₜ n) :
    (fun i ↦ (⌜(![t, u]) i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n)) =
      ![⌜t⌝, ⌜u⌝] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

variable (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]

@[simp] lemma set_eq_refl (t : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢ t ≐ₛ t := by
  have houter : T ⊢ ∀⁰ sEq #0 #0 := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff, sEq]
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ sEq #0 #0 : SetTheorySentence)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ((#'0) ≐ₛ (#'0)) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize! hint t

lemma set_eq_symm (t u : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢ (t ≐ₛ u) 🡒 (u ≐ₛ t) := by
  have houter : T ⊢ ∀⁰ ∀⁰ (sEq #1 #0 🡒 sEq #0 #1) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff, sEq]
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ (sEq #1 #0 🡒 sEq #0 #1) : SetTheorySentence)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒 ((#'0) ≐ₛ (#'1))) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize₂! hint u t

lemma set_eq_uniform_trans (t₁ t₂ t₃ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢ (t₁ ≐ₛ t₂) 🡒 (t₂ ≐ₛ t₃) 🡒 (t₁ ≐ₛ t₃) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ (sEq #2 #1 🡒 sEq #1 #0 🡒 sEq #2 #0) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff, sEq]
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ (sEq #2 #1 🡒 sEq #1 #0 🡒 sEq #2 #0) :
      SetTheorySentence)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ (((#'2) ≐ₛ (#'1)) 🡒 ((#'1) ≐ₛ (#'0)) 🡒 ((#'2) ≐ₛ (#'0))) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize₃! hint t₃ t₂ t₁

lemma subst_eq (t₁ t₂ u₁ u₂ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢
      (t₁ ≐ₛ t₂) 🡒 (u₁ ≐ₛ u₂) 🡒 (t₁ ≐ₛ u₁) 🡒 (t₂ ≐ₛ u₂) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 sEq #3 #1 🡒 sEq #2 #0) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff, sEq]
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 sEq #3 #1 🡒 sEq #2 #0) :
      SetTheorySentence)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
        (((#'3) ≐ₛ (#'2)) 🡒 ((#'1) ≐ₛ (#'0)) 🡒
          ((#'3) ≐ₛ (#'1)) 🡒 ((#'2) ≐ₛ (#'0))) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize₄! hint u₂ u₁ t₂ t₁

lemma subst_mem (t₁ t₂ u₁ u₂ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢
      (t₁ ≐ₛ t₂) 🡒 (u₁ ≐ₛ u₂) 🡒 (t₁ ∊ₛ u₁) 🡒 (t₂ ∊ₛ u₂) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 sMem #3 #1 🡒 sMem #2 #0) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    (simp [models_iff, sEq, sMem]; grind)
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 sMem #3 #1 🡒 sMem #2 #0) :
      SetTheorySentence)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
        (((#'3) ≐ₛ (#'2)) 🡒 ((#'1) ≐ₛ (#'0)) 🡒
          ((#'3) ∊ₛ (#'1)) 🡒 ((#'2) ∊ₛ (#'0))) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, sMem, eqAtom, memAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize₄! hint u₂ u₁ t₂ t₁

lemma subst_ne (t₁ t₂ u₁ u₂ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢
      (t₁ ≐ₛ t₂) 🡒 (u₁ ≐ₛ u₂) 🡒 (t₁ ≉ₛ u₁) 🡒 (t₂ ≉ₛ u₂) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 ∼sEq #3 #1 🡒 ∼sEq #2 #0) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    (simp [models_iff, sEq]; grind)
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 ∼sEq #3 #1 🡒 ∼sEq #2 #0) :
      SetTheorySentence)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
        (((#'3) ≐ₛ (#'2)) 🡒 ((#'1) ≐ₛ (#'0)) 🡒
          ((#'3) ≉ₛ (#'1)) 🡒 ((#'2) ≉ₛ (#'0))) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, eqAtom, neAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize₄! hint u₂ u₁ t₂ t₁

lemma subst_nmem (t₁ t₂ u₁ u₂ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢
      (t₁ ≐ₛ t₂) 🡒 (u₁ ≐ₛ u₂) 🡒 (t₁ ∉ₛ u₁) 🡒 (t₂ ∉ₛ u₂) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 ∼sMem #3 #1 🡒 ∼sMem #2 #0) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    (simp [models_iff, sEq, sMem]; grind)
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰
      (sEq #3 #2 🡒 sEq #1 #0 🡒 ∼sMem #3 #1 🡒 ∼sMem #2 #0) :
      SetTheorySentence)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
        (((#'3) ≐ₛ (#'2)) 🡒 ((#'1) ≐ₛ (#'0)) 🡒
          ((#'3) ∉ₛ (#'1)) 🡒 ((#'2) ∉ₛ (#'0))) := by
    rw [Sentence.typed_quote_def]
    simp [sEq, sMem, eqAtom, nmemAtom, Rew.q_emb, Rew.emb_bvar,
      quote_vec2_eta]
  rw [hq] at hint
  simpa using TProof.specialize₄! hint u₂ u₁ t₂ t₁

/-! ## Term replacement

`ℒₛₑₜ` has no function symbols, so an internal term of one bound variable
is either that variable or a free variable; the function case of the `𝚺₁`
induction is discharged by `isFunc_iff_Set`. -/

lemma term_replace_aux (t : V) :
    IsSemiterm ℒₛₑₜ 1 t →
    Provable T (^∀ ^∀ imp ℒₛₑₜ
      (^rel 2 ((setEqIndex : ℕ) : V) ?[^#1, ^#0])
      (^rel 2 ((setEqIndex : ℕ) : V)
        ?[termSubst ℒₛₑₜ (^#1 ∷ 0) t, termSubst ℒₛₑₜ (^#0 ∷ 0) t])) := by
  apply IsSemiterm.sigma1_induction
  · definability
  case hbvar =>
    intro z hz
    rcases lt_one_iff_eq_zero.mp hz with rfl
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒 ((#'1) ≐ₛ (#'0))) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [Bootstrapping.Semiformula.val_all] using this
    have houter : T ⊢ ∀⁰ ∀⁰ (sEq #1 #0 🡒 sEq #1 #0) := by
      refine SetTheory.provable_of_models.{0} T _ ?_
      intro M _ _ _
      simp [models_iff, sEq]
    have hint := internal_provable_of_outer_provable (V := V) houter
    have hq : (⌜(∀⁰ ∀⁰ (sEq #1 #0 🡒 sEq #1 #0) : SetTheorySentence)⌝ :
        Bootstrapping.Formula V ℒₛₑₜ) =
        ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒 ((#'1) ≐ₛ (#'0))) := by
      rw [Sentence.typed_quote_def]
      simp [sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]
    rwa [hq] at hint
  case hfvar =>
    intro x
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒 ((&'x) ≐ₛ (&'x))) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [Bootstrapping.Semiformula.val_all] using this
    suffices T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒 ((&'(x + 1 + 1)) ≐ₛ (&'(x + 1 + 1))) by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free]
    apply Entailment.dhyp! (set_eq_refl T _)
  case hfunc =>
    intro k F v hF hv ih
    exact absurd hF isFunc_iff_Set

lemma term_replace (t : Bootstrapping.Semiterm V ℒₛₑₜ 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
      (t.subst ![#'1] ≐ₛ t.subst ![#'0])) := by
  apply (tprovable_iff_provable (T := T)).mpr
  simpa using term_replace_aux T t.val

lemma term_replace' (t : Bootstrapping.Semiterm V ℒₛₑₜ 1)
    (u₁ u₂ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢ (u₁ ≐ₛ u₂) 🡒 (t.subst ![u₁] ≐ₛ t.subst ![u₂]) := by
  have := TProof.specialize₂! (term_replace T t) u₂ u₁
  simpa [Bootstrapping.Semiterm.substs_substs] using this

/-! ## Replacement at the four atoms -/

lemma replace_eq (t u : Bootstrapping.Semiterm V ℒₛₑₜ 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
      (t ≐ₛ u).subst ![#'1] 🡒 (t ≐ₛ u).subst ![#'0]) := by
  suffices
      T.internalize V ⊢
        ((&'1) ≐ₛ (&'0)) 🡒
        (t⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'1]) 🡒
        (t⇞⇞.subst ![&'0] ≐ₛ u⇞⇞.subst ![&'0]) by
    apply TProof.all₂!
    simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
      Bootstrapping.Semiterm.shift_substs, Bootstrapping.Semiterm.substs_substs]
  let Γ : List (Bootstrapping.Formula V ℒₛₑₜ) :=
    [t⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'1], (&'1) ≐ₛ (&'0)]
  suffices
      Γ ⊢[T.internalize V] t⇞⇞.subst ![&'0] ≐ₛ u⇞⇞.subst ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ≐ₛ t⇞⇞.subst ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V] u⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_eq T (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
      (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_mem (t u : Bootstrapping.Semiterm V ℒₛₑₜ 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
      (t ∊ₛ u).subst ![#'1] 🡒 (t ∊ₛ u).subst ![#'0]) := by
  suffices
      T.internalize V ⊢
        ((&'1) ≐ₛ (&'0)) 🡒
        (t⇞⇞.subst ![&'1] ∊ₛ u⇞⇞.subst ![&'1]) 🡒
        (t⇞⇞.subst ![&'0] ∊ₛ u⇞⇞.subst ![&'0]) by
    apply TProof.all₂!
    simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
      Bootstrapping.Semiterm.shift_substs, Bootstrapping.Semiterm.substs_substs]
  let Γ : List (Bootstrapping.Formula V ℒₛₑₜ) :=
    [t⇞⇞.subst ![&'1] ∊ₛ u⇞⇞.subst ![&'1], (&'1) ≐ₛ (&'0)]
  suffices
      Γ ⊢[T.internalize V] t⇞⇞.subst ![&'0] ∊ₛ u⇞⇞.subst ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ∊ₛ u⇞⇞.subst ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ≐ₛ t⇞⇞.subst ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V] u⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_mem T (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
      (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_ne (t u : Bootstrapping.Semiterm V ℒₛₑₜ 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
      (t ≉ₛ u).subst ![#'1] 🡒 (t ≉ₛ u).subst ![#'0]) := by
  suffices
      T.internalize V ⊢
        ((&'1) ≐ₛ (&'0)) 🡒
        (t⇞⇞.subst ![&'1] ≉ₛ u⇞⇞.subst ![&'1]) 🡒
        (t⇞⇞.subst ![&'0] ≉ₛ u⇞⇞.subst ![&'0]) by
    apply TProof.all₂!
    simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
      Bootstrapping.Semiterm.shift_substs, Bootstrapping.Semiterm.substs_substs]
  let Γ : List (Bootstrapping.Formula V ℒₛₑₜ) :=
    [t⇞⇞.subst ![&'1] ≉ₛ u⇞⇞.subst ![&'1], (&'1) ≐ₛ (&'0)]
  suffices
      Γ ⊢[T.internalize V] t⇞⇞.subst ![&'0] ≉ₛ u⇞⇞.subst ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ≉ₛ u⇞⇞.subst ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ≐ₛ t⇞⇞.subst ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V] u⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_ne T (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
      (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_nmem (t u : Bootstrapping.Semiterm V ℒₛₑₜ 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
      (t ∉ₛ u).subst ![#'1] 🡒 (t ∉ₛ u).subst ![#'0]) := by
  suffices
      T.internalize V ⊢
        ((&'1) ≐ₛ (&'0)) 🡒
        (t⇞⇞.subst ![&'1] ∉ₛ u⇞⇞.subst ![&'1]) 🡒
        (t⇞⇞.subst ![&'0] ∉ₛ u⇞⇞.subst ![&'0]) by
    apply TProof.all₂!
    simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
      Bootstrapping.Semiterm.shift_substs, Bootstrapping.Semiterm.substs_substs]
  let Γ : List (Bootstrapping.Formula V ℒₛₑₜ) :=
    [t⇞⇞.subst ![&'1] ∉ₛ u⇞⇞.subst ![&'1], (&'1) ≐ₛ (&'0)]
  suffices
      Γ ⊢[T.internalize V] t⇞⇞.subst ![&'0] ∉ₛ u⇞⇞.subst ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ∉ₛ u⇞⇞.subst ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V] t⇞⇞.subst ![&'1] ≐ₛ t⇞⇞.subst ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V] u⇞⇞.subst ![&'1] ≐ₛ u⇞⇞.subst ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_nmem T (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
      (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

/-! ## Replacement for arbitrary model-coded formulas

The `𝚺₁` structural induction on the coded formula.  The relation cases
split by `isRel_iff_Set` into the four atom lemmas above; the connective
and quantifier cases are language-independent transliterations of
Foundation's `Bootstrapping.Arithmetic.replace_aux`. -/

lemma replace_aux (φ : V) :
    IsSemiformula ℒₛₑₜ 1 φ →
    Provable T (^∀ ^∀ imp ℒₛₑₜ
      (^rel 2 ((setEqIndex : ℕ) : V) ?[^#1, ^#0])
      (imp ℒₛₑₜ (subst ℒₛₑₜ (^#1 ∷ 0) φ) (subst ℒₛₑₜ (^#0 ∷ 0) φ))) := by
  apply IsFormula.sigma1_structural_induction₂_ss
  · definability
  case hand =>
    intro p q hp hq ihp ihq
    let φ : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⟨p, by simpa using hp⟩
    let ψ : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⟨q, by simpa using hq⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        (φ ⋏ ψ).subst ![#'1] 🡒 (φ ⋏ ψ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [-Bootstrapping.Semiformula.substs_and, -substs_and, φ, ψ]
        using this
    suffices
        T.internalize V ⊢
          ((&'1) ≐ₛ (&'0)) 🡒
            φ⤉⤉.subst ![&'1] ⋏ ψ⤉⤉.subst ![&'1] 🡒
            φ⤉⤉.subst ![&'0] ⋏ ψ⤉⤉.subst ![&'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs]
    have ihφ : T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihp
    have ihψ : T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        ψ.subst ![#'1] 🡒 ψ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihq
    have ihφ :
        T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒
          φ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs] using this
    have ihψ :
        T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒
          ψ⤉⤉.subst ![&'1] 🡒 ψ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs] using this
    cl_prover [ihφ, ihψ]
  case hor =>
    intro p q hp hq ihp ihq
    let φ : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⟨p, by simpa using hp⟩
    let ψ : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⟨q, by simpa using hq⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        (φ ⋎ ψ).subst ![#'1] 🡒 (φ ⋎ ψ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa [-Bootstrapping.Semiformula.substs_or, -substs_or, φ, ψ]
        using this
    suffices
        T.internalize V ⊢
          ((&'1) ≐ₛ (&'0)) 🡒
            φ⤉⤉.subst ![&'1] ⋎ ψ⤉⤉.subst ![&'1] 🡒
            φ⤉⤉.subst ![&'0] ⋎ ψ⤉⤉.subst ![&'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs]
    have ihφ : T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihp
    have ihψ : T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        ψ.subst ![#'1] 🡒 ψ.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ihq
    have ihφ :
        T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒
          φ⤉⤉.subst ![&'1] 🡒 φ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs] using this
    have ihψ :
        T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒
          ψ⤉⤉.subst ![&'1] 🡒 ψ⤉⤉.subst ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs] using this
    cl_prover [ihφ, ihψ]
  case hverum =>
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒 ⊤ 🡒 ⊤) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa using this
    suffices Theory.internalize V T ⊢ ((&'1) ≐ₛ (&'0)) 🡒 ⊤ 🡒 ⊤ by
      apply TProof.all₂!
      simpa
    apply dhyp!
    exact CV!
  case hfalsum =>
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒 ⊥ 🡒 ⊥) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa using this
    suffices Theory.internalize V T ⊢ ((&'1) ≐ₛ (&'0)) 🡒 ⊥ 🡒 ⊥ by
      apply TProof.all₂!
      simpa
    apply dhyp!
    exact efq!
  case hrel =>
    intro k R v hR hv
    rcases isRel_iff_Set.mp hR with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · let t : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, Bootstrapping.Arithmetic.vec2_eq hv.lh]
      suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
          (t ≐ₛ u).subst ![#'1] 🡒 (t ≐ₛ u).subst ![#'0]) by
        have := (tprovable_iff_provable (T := T)).mp this
        simpa [-eqAtom_subst, veq] using! this
      simpa using replace_eq T t u
    · let t : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, Bootstrapping.Arithmetic.vec2_eq hv.lh]
      suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
          (t ∊ₛ u).subst ![#'1] 🡒 (t ∊ₛ u).subst ![#'0]) by
        have := (tprovable_iff_provable (T := T)).mp this
        simpa [-memAtom_subst, veq] using! this
      simpa using replace_mem T t u
  case hnrel =>
    intro k R v hR hv
    rcases isRel_iff_Set.mp hR with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · let t : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, Bootstrapping.Arithmetic.vec2_eq hv.lh]
      suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
          (t ≉ₛ u).subst ![#'1] 🡒 (t ≉ₛ u).subst ![#'0]) by
        have := (tprovable_iff_provable (T := T)).mp this
        simpa [-neAtom_subst, veq] using! this
      simpa using replace_ne T t u
    · let t : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Bootstrapping.Semiterm V ℒₛₑₜ 1 :=
        ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, Bootstrapping.Arithmetic.vec2_eq hv.lh]
      suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
          (t ∉ₛ u).subst ![#'1] 🡒 (t ∉ₛ u).subst ![#'0]) by
        have := (tprovable_iff_provable (T := T)).mp this
        simpa [-nmemAtom_subst, veq] using! this
      simpa using replace_nmem T t u
  case hall =>
    intro p hp ih
    let φ : Bootstrapping.Semiformula V ℒₛₑₜ 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        (∀⁰ φ).subst ![#'1] 🡒 (∀⁰ φ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one,
        Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
        val_eqAtom, Bootstrapping.Semiterm.bvar_val, Fin.coe_ofNat_eq_mod,
        Nat.mod_succ, Nat.cast_one, Nat.zero_mod, Nat.cast_zero,
        Bootstrapping.Semiformula.val_substs,
        Bootstrapping.SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, Bootstrapping.SemitermVec.val_nil] using this
    have ih : T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        φ⤉⤉.free1.subst ![#'1] 🡒 φ⤉⤉.free1.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒
          ∀⁰ φ⤉⤉.subst ![#'0, &'1] 🡒 ∀⁰ φ⤉⤉.subst ![#'0, &'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs]
    apply deduct'!
    apply TProof.all_imp_all!
    apply deductInv'!
    simpa [Bootstrapping.Semiformula.free1, Bootstrapping.Semiformula.free,
      Bootstrapping.SemitermVec.q, Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs, one_add_one_eq_two]
    using TProof.specialize₂! ih (&'1) (&'2)
  case hexs =>
    intro p hp ih
    let φ : Bootstrapping.Semiformula V ℒₛₑₜ 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        (∃⁰ φ).subst ![#'1] 🡒 (∃⁰ φ).subst ![#'0]) by
      have := (tprovable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one,
        Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
        val_eqAtom, Bootstrapping.Semiterm.bvar_val, Fin.coe_ofNat_eq_mod,
        Nat.mod_succ, Nat.cast_one, Nat.zero_mod, Nat.cast_zero,
        Bootstrapping.Semiformula.val_substs,
        Bootstrapping.SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, Bootstrapping.SemitermVec.val_nil] using! this
    have ih : T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
        φ⤉⤉.free1.subst ![#'1] 🡒 φ⤉⤉.free1.subst ![#'0]) := by
      apply (tprovable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢ ((&'1) ≐ₛ (&'0)) 🡒
          ∃⁰ φ⤉⤉.subst ![#'0, &'1] 🡒 ∃⁰ φ⤉⤉.subst ![#'0, &'0] by
      apply TProof.all₂!
      simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs]
    apply deduct'!
    apply TProof.exs_imp_exs!
    apply deductInv'!
    simpa [Bootstrapping.Semiformula.free1, Bootstrapping.Semiformula.free,
      Bootstrapping.SemitermVec.q, Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs, one_add_one_eq_two]
      using TProof.specialize₂! ih (&'1) (&'2)

/-- Equality replacement for a model-coded unary `ℒₛₑₜ` formula, in
universally quantified form. -/
lemma setReplace' (φ : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    T.internalize V ⊢ ∀⁰ ∀⁰ (((#'1) ≐ₛ (#'0)) 🡒
      φ.subst ![#'1] 🡒 φ.subst ![#'0]) := by
  apply (tprovable_iff_provable (T := T)).mpr
  simpa using replace_aux T φ.val

/-- **Equality replacement for a model-coded unary `ℒₛₑₜ` formula.**  The
formula's Gödel code may be a nonstandard element of `V`. -/
lemma setReplace (φ : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (u₁ u₂ : Bootstrapping.Term V ℒₛₑₜ) :
    T.internalize V ⊢ (u₁ ≐ₛ u₂) 🡒 φ.subst ![u₁] 🡒 φ.subst ![u₂] := by
  have := TProof.specialize₂! (setReplace' T φ) u₂ u₁
  simpa [Bootstrapping.Semiformula.substs_substs] using this

/-! ## The internal congruence formulas

The translated shape of `Theory.Eq.relExt` at a placeholder of arity `a`:
two universally quantified `a`-tuples, a conjunction of coordinatewise
equalities, and the transported relation, with the placeholder specialized
to a model-coded `K`. -/

/-- The first quantified tuple of a `relExt` instance. -/
noncomputable def leftTuple (a : ℕ) :
    Bootstrapping.SemitermVec V ℒₛₑₜ a (a + a) :=
  fun j ↦ Bootstrapping.Semiterm.bvar (j.addCast a)

/-- The second quantified tuple of a `relExt` instance. -/
noncomputable def rightTuple (a : ℕ) :
    Bootstrapping.SemitermVec V ℒₛₑₜ a (a + a) :=
  fun j ↦ Bootstrapping.Semiterm.bvar (j.addNat a)

/-- The coordinatewise-equality antecedent of a `relExt` instance. -/
noncomputable def congruenceContext (a : ℕ) :
    Bootstrapping.Semiformula V ℒₛₑₜ (a + a) :=
  Matrix.conj fun j : Fin a ↦ (leftTuple a j ≐ₛ rightTuple a j)

/-- The internal congruence law for a model-coded `a`-ary formula: the
translated shape of the placeholder congruence sentence. -/
noncomputable def congruenceFormula (a : ℕ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ a) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  ∀⁰* (congruenceContext a 🡒 K.subst (leftTuple a) 🡒 K.subst (rightTuple a))

/-- The unary congruence law, discharged from `setReplace`. -/
lemma congruenceProof₁ (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    T.internalize V ⊢ congruenceFormula 1 K := by
  have hleft : leftTuple (V := V) 1 = ![#'0] := by
    funext j
    rcases Fin.eq_zero j with rfl
    rfl
  have hright : rightTuple (V := V) 1 = ![#'1] := by
    funext j
    rcases Fin.eq_zero j with rfl
    rfl
  have hshape : congruenceFormula 1 K =
      ∀⁰ ∀⁰ ((((#'0) ≐ₛ (#'1)) ⋏ ⊤) 🡒 K.subst ![#'0] 🡒 K.subst ![#'1]) := by
    unfold congruenceFormula congruenceContext
    rw [hleft, hright]
    rfl
  rw [hshape]
  apply TProof.all₂!
  suffices T.internalize V ⊢
      (((&'0) ≐ₛ (&'1)) ⋏ ⊤) 🡒 K⤉⤉.subst ![&'0] 🡒 K⤉⤉.subst ![&'1] by
    simpa [Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs]
  have h := setReplace T K⤉⤉ (&'0) (&'1)
  cl_prover [h]

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
/-- The nullary congruence law: both tuples are empty, and the substitution
by the empty vector is the identity. -/
lemma congruenceProof₀ (K : Bootstrapping.Semiformula V ℒₛₑₜ 0) :
    T.internalize V ⊢ congruenceFormula 0 K := by
  have hshape : congruenceFormula 0 K = (⊤ 🡒 K 🡒 K) := by
    unfold congruenceFormula congruenceContext
    have hleft : K.subst (leftTuple (V := V) 0) = K := by
      have h : leftTuple (V := V) 0 = ![] := by
        funext j
        exact j.elim0
      rw [h]
      simp
    have hright : K.subst (rightTuple (V := V) 0) = K := by
      have h : rightTuple (V := V) 0 = ![] := by
        funext j
        exact j.elim0
      rw [h]
      simp
    rw [hleft, hright]
    rfl
  rw [hshape]
  cl_prover

/-! ### The binary discharge -/

section binary

private noncomputable def genTuple₄ : Fin 4 → Bootstrapping.Term V ℒₛₑₜ :=
  ![.fvar 0, .fvar 1, .fvar (1 + 1), .fvar (1 + 1 + 1)]

/- `TProof` provides one- and two-variable generalization helpers; this
four-variable specialization keeps the bookkeeping independent of the
(potentially nonstandard) formula being generalized. -/
omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
private lemma allFour {φ : Bootstrapping.Semiformula V ℒₛₑₜ 4}
    (h : T.internalize V ⊢
      φ.shift.shift.shift.shift.subst genTuple₄) :
    T.internalize V ⊢ ∀⁰* φ := by
  simp only [allClosure_succ, allClosure_zero]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,
    genTuple₄] using h

private noncomputable def shiftK₂ (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 2 :=
  K.shift.shift.shift.shift

private noncomputable def left₂ : Fin 2 → Bootstrapping.Term V ℒₛₑₜ :=
  ![.fvar 0, .fvar 1]

private noncomputable def right₂ : Fin 2 → Bootstrapping.Term V ℒₛₑₜ :=
  ![.fvar (1 + 1), .fvar (1 + 1 + 1)]

private noncomputable def mid₂ : Fin 2 → Bootstrapping.Term V ℒₛₑₜ :=
  ![right₂ 0, left₂ 1]

private noncomputable def coord₂₀ (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  (shiftK₂ K).subst ![Bootstrapping.Semiterm.bvar 0, (left₂ 1).bShift]

private noncomputable def coord₂₁ (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  (shiftK₂ K).subst ![(right₂ 0).bShift, Bootstrapping.Semiterm.bvar 0]

private lemma freeBinaryProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    T.internalize V ⊢
      ((left₂ 0 ≐ₛ right₂ 0) ⋏ ((left₂ 1 ≐ₛ right₂ 1) ⋏ ⊤)) 🡒
        (shiftK₂ K).subst left₂ 🡒 (shiftK₂ K).subst right₂ := by
  have h₀ := setReplace T (coord₂₀ K) (left₂ 0) (right₂ 0)
  have h₁ := setReplace T (coord₂₁ K) (left₂ 1) (right₂ 1)
  have h₀' : T.internalize V ⊢
      (left₂ 0 ≐ₛ right₂ 0) 🡒
        (shiftK₂ K).subst left₂ 🡒 (shiftK₂ K).subst mid₂ := by
    simpa [coord₂₀, Bootstrapping.Semiformula.substs_substs,
      left₂, right₂, mid₂, Function.comp_def,
      Matrix.constant_eq_singleton] using h₀
  have h₁' : T.internalize V ⊢
      (left₂ 1 ≐ₛ right₂ 1) 🡒
        (shiftK₂ K).subst mid₂ 🡒 (shiftK₂ K).subst right₂ := by
    simpa [coord₂₁, Bootstrapping.Semiformula.substs_substs,
      left₂, right₂, mid₂, Function.comp_def,
      Matrix.constant_eq_singleton] using h₁
  cl_prover [h₀', h₁']

private lemma genTuple₄_left (j : Fin 2) :
    ((leftTuple (V := V) 2)
        j).shift.shift.shift.shift.subst genTuple₄ = left₂ j := by
  cases j using Fin.cases with
  | zero =>
      simp only [leftTuple, Bootstrapping.Semiterm.shift_bvar,
        Bootstrapping.Semiterm.substs_bvar, left₂]
      rw [show Fin.addCast 2 (0 : Fin 2) = (0 : Fin 4) by
        apply Fin.ext
        rfl]
      rfl
  | succ j =>
      rcases Fin.eq_zero j with rfl
      simp only [leftTuple, Bootstrapping.Semiterm.shift_bvar,
        Bootstrapping.Semiterm.substs_bvar, left₂]
      rw [show Fin.addCast 2 (Fin.succ (0 : Fin 1)) = (1 : Fin 4) by
        apply Fin.ext
        rfl]
      rfl

private lemma genTuple₄_right (j : Fin 2) :
    ((rightTuple (V := V) 2)
        j).shift.shift.shift.shift.subst genTuple₄ = right₂ j := by
  cases j using Fin.cases with
  | zero => simp [rightTuple, genTuple₄, right₂]
  | succ j =>
      rcases Fin.eq_zero j with rfl
      simp [rightTuple, genTuple₄, right₂]

private lemma generalize_binaryBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (congruenceContext 2 🡒
        K.subst (leftTuple 2) 🡒
        K.subst (rightTuple 2)).shift.shift.shift.shift.subst genTuple₄ =
      ((left₂ 0 ≐ₛ right₂ 0) ⋏ ((left₂ 1 ≐ₛ right₂ 1) ⋏ ⊤)) 🡒
        (shiftK₂ K).subst left₂ 🡒 (shiftK₂ K).subst right₂ := by
  have hK : ∀ w : Bootstrapping.SemitermVec V ℒₛₑₜ 2 4,
      (K.subst w).shift.shift.shift.shift.subst genTuple₄ =
        (shiftK₂ K).subst
          (fun j ↦ (w j).shift.shift.shift.shift.subst genTuple₄) := by
    intro w
    simp only [Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs, shiftK₂]
    congr 1
  rw [show congruenceContext (V := V) 2 =
      (leftTuple 2 0 ≐ₛ rightTuple 2 0) ⋏
        ((leftTuple 2 1 ≐ₛ rightTuple 2 1) ⋏ ⊤) from rfl]
  simp only [Bootstrapping.Semiformula.shift_imp,
    Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.shift_verum,
    eqAtom_shift,
    Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,
    Bootstrapping.Semiformula.substs_verum,
    eqAtom_subst,
    hK, genTuple₄_left, genTuple₄_right]

/-- The binary congruence law, discharged from `setReplace` coordinate by
coordinate. -/
lemma congruenceProof₂ (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    T.internalize V ⊢ congruenceFormula 2 K := by
  unfold congruenceFormula
  apply allFour
  rw [generalize_binaryBody]
  exact freeBinaryProof T K

end binary

/-! ### The ternary discharge -/

section ternary

private noncomputable def genTuple₆ : Fin 6 → Bootstrapping.Term V ℒₛₑₜ :=
  ![.fvar 0, .fvar 1, .fvar (1 + 1), .fvar (1 + 1 + 1),
    .fvar (1 + 1 + 1 + 1), .fvar (1 + 1 + 1 + 1 + 1)]

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
private lemma allSix {φ : Bootstrapping.Semiformula V ℒₛₑₜ 6}
    (h : T.internalize V ⊢
      φ.shift.shift.shift.shift.shift.shift.subst genTuple₆) :
    T.internalize V ⊢ ∀⁰* φ := by
  simp only [allClosure_succ, allClosure_zero]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simp [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q]
  apply TProof.all!
  simpa [Bootstrapping.Semiformula.free, Bootstrapping.SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,
    genTuple₆] using h

private noncomputable def shiftK₃ (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    Bootstrapping.Semiformula V ℒₛₑₜ 3 :=
  K.shift.shift.shift.shift.shift.shift

private noncomputable def left₃ : Fin 3 → Bootstrapping.Term V ℒₛₑₜ :=
  ![.fvar 0, .fvar 1, .fvar (1 + 1)]

private noncomputable def right₃ : Fin 3 → Bootstrapping.Term V ℒₛₑₜ :=
  ![.fvar (1 + 1 + 1), .fvar (1 + 1 + 1 + 1), .fvar (1 + 1 + 1 + 1 + 1)]

private noncomputable def afterFirst₃ : Fin 3 → Bootstrapping.Term V ℒₛₑₜ :=
  ![right₃ 0, left₃ 1, left₃ 2]

private noncomputable def afterSecond₃ : Fin 3 → Bootstrapping.Term V ℒₛₑₜ :=
  ![right₃ 0, right₃ 1, left₃ 2]

private noncomputable def coord₃₀ (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  (shiftK₃ K).subst
    ![Bootstrapping.Semiterm.bvar 0, (left₃ 1).bShift, (left₃ 2).bShift]

private noncomputable def coord₃₁ (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  (shiftK₃ K).subst
    ![(right₃ 0).bShift, Bootstrapping.Semiterm.bvar 0, (left₃ 2).bShift]

private noncomputable def coord₃₂ (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  (shiftK₃ K).subst
    ![(right₃ 0).bShift, (right₃ 1).bShift, Bootstrapping.Semiterm.bvar 0]

private lemma freeTernaryProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    T.internalize V ⊢
      ((left₃ 0 ≐ₛ right₃ 0) ⋏
          ((left₃ 1 ≐ₛ right₃ 1) ⋏ ((left₃ 2 ≐ₛ right₃ 2) ⋏ ⊤))) 🡒
        (shiftK₃ K).subst left₃ 🡒 (shiftK₃ K).subst right₃ := by
  have h₀ := setReplace T (coord₃₀ K) (left₃ 0) (right₃ 0)
  have h₁ := setReplace T (coord₃₁ K) (left₃ 1) (right₃ 1)
  have h₂ := setReplace T (coord₃₂ K) (left₃ 2) (right₃ 2)
  have h₀' : T.internalize V ⊢
      (left₃ 0 ≐ₛ right₃ 0) 🡒
        (shiftK₃ K).subst left₃ 🡒 (shiftK₃ K).subst afterFirst₃ := by
    simpa [coord₃₀, Bootstrapping.Semiformula.substs_substs,
      left₃, right₃, afterFirst₃, Function.comp_def,
      Matrix.constant_eq_singleton] using h₀
  have h₁' : T.internalize V ⊢
      (left₃ 1 ≐ₛ right₃ 1) 🡒
        (shiftK₃ K).subst afterFirst₃ 🡒 (shiftK₃ K).subst afterSecond₃ := by
    simpa [coord₃₁, Bootstrapping.Semiformula.substs_substs,
      left₃, right₃, afterFirst₃, afterSecond₃, Function.comp_def,
      Matrix.constant_eq_singleton] using h₁
  have h₂' : T.internalize V ⊢
      (left₃ 2 ≐ₛ right₃ 2) 🡒
        (shiftK₃ K).subst afterSecond₃ 🡒 (shiftK₃ K).subst right₃ := by
    simpa [coord₃₂, Bootstrapping.Semiformula.substs_substs,
      left₃, right₃, afterSecond₃, Function.comp_def,
      Matrix.constant_eq_singleton] using h₂
  let context : Bootstrapping.Formula V ℒₛₑₜ :=
    (left₃ 0 ≐ₛ right₃ 0) ⋏
      ((left₃ 1 ≐ₛ right₃ 1) ⋏ ((left₃ 2 ≐ₛ right₃ 2) ⋏ ⊤))
  let initial : Bootstrapping.Formula V ℒₛₑₜ := (shiftK₃ K).subst left₃
  let Γ : List (Bootstrapping.Formula V ℒₛₑₜ) := [initial, context]
  suffices Γ ⊢[T.internalize V] (shiftK₃ K).subst right₃ by
    apply deduct'!
    apply deduct!
    simpa [Γ, initial, context] using this
  have hinitial : Γ ⊢[T.internalize V] (shiftK₃ K).subst left₃ := by
    simpa [Γ, initial] using
      (by_axm₀! :
        ((shiftK₃ K).subst left₃ :: context :: []) ⊢[T.internalize V]
          (shiftK₃ K).subst left₃)
  have hcontext : Γ ⊢[T.internalize V] context := by
    simpa [Γ, initial] using
      (by_axm₁! :
        ((shiftK₃ K).subst left₃ :: context :: []) ⊢[T.internalize V] context)
  have heq₀ : Γ ⊢[T.internalize V] left₃ 0 ≐ₛ right₃ 0 :=
    K!_left hcontext
  have htail₀ : Γ ⊢[T.internalize V]
      (left₃ 1 ≐ₛ right₃ 1) ⋏ ((left₃ 2 ≐ₛ right₃ 2) ⋏ ⊤) :=
    K!_right hcontext
  have heq₁ : Γ ⊢[T.internalize V] left₃ 1 ≐ₛ right₃ 1 :=
    K!_left htail₀
  have htail₁ : Γ ⊢[T.internalize V] (left₃ 2 ≐ₛ right₃ 2) ⋏ ⊤ :=
    K!_right htail₀
  have heq₂ : Γ ⊢[T.internalize V] left₃ 2 ≐ₛ right₃ 2 :=
    K!_left htail₁
  have hafterFirst : Γ ⊢[T.internalize V] (shiftK₃ K).subst afterFirst₃ :=
    of'! h₀' ⨀ heq₀ ⨀ hinitial
  have hafterSecond : Γ ⊢[T.internalize V] (shiftK₃ K).subst afterSecond₃ :=
    of'! h₁' ⨀ heq₁ ⨀ hafterFirst
  exact of'! h₂' ⨀ heq₂ ⨀ hafterSecond

private lemma genTuple₆_left (j : Fin 3) :
    ((leftTuple (V := V) 3)
        j).shift.shift.shift.shift.shift.shift.subst genTuple₆ =
      left₃ j := by
  cases j using Fin.cases with
  | zero =>
      simp only [leftTuple, Bootstrapping.Semiterm.shift_bvar,
        Bootstrapping.Semiterm.substs_bvar, left₃]
      rw [show Fin.addCast 3 (0 : Fin 3) = (0 : Fin 6) by
        apply Fin.ext
        rfl]
      rfl
  | succ j =>
      cases j using Fin.cases with
      | zero =>
          simp only [leftTuple, Bootstrapping.Semiterm.shift_bvar,
            Bootstrapping.Semiterm.substs_bvar, left₃]
          rw [show Fin.addCast 3 (Fin.succ (0 : Fin 2)) = (1 : Fin 6) by
            apply Fin.ext
            rfl]
          rfl
      | succ j =>
          rcases Fin.eq_zero j with rfl
          simp only [leftTuple, Bootstrapping.Semiterm.shift_bvar,
            Bootstrapping.Semiterm.substs_bvar, left₃]
          rw [show Fin.addCast 3 ((Fin.succ (0 : Fin 1)).succ) = (2 : Fin 6) by
            apply Fin.ext
            rfl]
          rfl

private lemma genTuple₆_right (j : Fin 3) :
    ((rightTuple (V := V) 3)
        j).shift.shift.shift.shift.shift.shift.subst genTuple₆ =
      right₃ j := by
  cases j using Fin.cases with
  | zero => simp [rightTuple, genTuple₆, right₃]
  | succ j =>
      cases j using Fin.cases with
      | zero => simp [rightTuple, genTuple₆, right₃]
      | succ j =>
          rcases Fin.eq_zero j with rfl
          simp [rightTuple, genTuple₆, right₃]

private lemma generalize_ternaryBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    (congruenceContext 3 🡒
        K.subst (leftTuple 3) 🡒
        K.subst (rightTuple 3)).shift.shift.shift.shift.shift.shift.subst
          genTuple₆ =
      ((left₃ 0 ≐ₛ right₃ 0) ⋏
          ((left₃ 1 ≐ₛ right₃ 1) ⋏ ((left₃ 2 ≐ₛ right₃ 2) ⋏ ⊤))) 🡒
        (shiftK₃ K).subst left₃ 🡒 (shiftK₃ K).subst right₃ := by
  have hK : ∀ w : Bootstrapping.SemitermVec V ℒₛₑₜ 3 6,
      (K.subst w).shift.shift.shift.shift.shift.shift.subst genTuple₆ =
        (shiftK₃ K).subst
          (fun j ↦
            (w j).shift.shift.shift.shift.shift.shift.subst genTuple₆) := by
    intro w
    simp only [Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs, shiftK₃]
    congr 1
  rw [show congruenceContext (V := V) 3 =
      (leftTuple 3 0 ≐ₛ rightTuple 3 0) ⋏
        ((leftTuple 3 1 ≐ₛ rightTuple 3 1) ⋏
          ((leftTuple 3 2 ≐ₛ rightTuple 3 2) ⋏ ⊤)) from rfl]
  simp only [Bootstrapping.Semiformula.shift_imp,
    Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.shift_verum,
    eqAtom_shift,
    Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,
    Bootstrapping.Semiformula.substs_verum,
    eqAtom_subst,
    hK, genTuple₆_left, genTuple₆_right]

/-- The ternary congruence law, discharged from `setReplace` coordinate by
coordinate.  This is the arity of the canonical truth-predicate slot
assignment (`ZFCinPA.LevelCodeTower`). -/
lemma congruenceProof₃ (K : Bootstrapping.Semiformula V ℒₛₑₜ 3) :
    T.internalize V ⊢ congruenceFormula 3 K := by
  unfold congruenceFormula
  apply allSix
  rw [generalize_ternaryBody]
  exact freeTernaryProof T K

end ternary

/-! ## Translating the placeholder congruence sentences

The source congruence sentence for the `i`-th placeholder specializes,
under the placeholder translation of `ZFCinPA.SetPlaceholders`, to exactly
`congruenceFormula (arities i) (Ks i)`. -/

section translate

open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient

variable {k : ℕ} {arities : Fin k → ℕ}

/-- The congruence sentence, restated with explicit `srcEq`/`srcP` atoms:
the operator layer of `Theory.Eq.relExt` unfolds to raw relation atoms. -/
lemma relExt_eq_src (i : Fin k) :
    setPlaceholderCongruenceSentence k arities i =
      ∀⁰* ((Matrix.conj fun j : Fin (arities i) ↦
              srcEq (#(j.addCast (arities i))) (#(j.addNat (arities i)))) 🡒
            srcP i (fun j ↦ #(j.addCast (arities i))) 🡒
            srcP i (fun j ↦ #(j.addNat (arities i)))) := rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Specialization commutes with the universal closure. -/
lemma translateFormula_allClosure
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {m : ℕ} (p : Semiproposition (setTemplateLanguage k arities) m) :
    translateFormula Ks (∀⁰* p) = ∀⁰* translateFormula Ks p := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [allClosure_succ, ih,
        show translateFormula Ks (∀⁰ p) = ∀⁰ translateFormula Ks p from rfl,
        ← allClosure_succ]

/-- Specialization commutes with finite conjunction. -/
lemma translateFormula_conj
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {m ℓ : ℕ} (v : Fin m → Semiproposition (setTemplateLanguage k arities) ℓ) :
    translateFormula Ks (Matrix.conj v) =
      Matrix.conj fun j ↦ translateFormula Ks (v j) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show Matrix.conj v = v 0 ⋏ Matrix.conj (Matrix.vecTail v) from rfl,
        show translateFormula Ks (v 0 ⋏ Matrix.conj (Matrix.vecTail v)) =
          translateFormula Ks (v 0) ⋏
            translateFormula Ks (Matrix.conj (Matrix.vecTail v)) from rfl,
        ih]
      rfl

/-- **The congruence sentence specializes to the internal congruence
formula.**  The source-level `relExt` at the `i`-th placeholder translates
to `congruenceFormula` at the model-coded interpretation `Ks i`. -/
theorem translate_setPlaceholderCongruenceSentence
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (i : Fin k) :
    translateFormula Ks
        (Rewriting.emb (setPlaceholderCongruenceSentence k arities i) :
          Proposition (setTemplateLanguage k arities)) =
      congruenceFormula (arities i) (Ks i) := by
  rw [relExt_eq_src, Rewriting.emb_allClosure,
    translateFormula_allClosure]
  unfold congruenceFormula
  congr 1
  simp only [LogicalConnective.HomClass.map_imply, translateFormula_imp]
  congr 1
  rw [Matrix.hom_conj, translateFormula_conj]
  unfold congruenceContext
  congr 1

/-- Specialization of the full conjunctive congruence antecedent. -/
theorem translate_setPlaceholderCongruence
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) :
    translateFormula Ks
        (Rewriting.emb (setPlaceholderCongruence k arities) :
          Proposition (setTemplateLanguage k arities)) =
      Matrix.conj fun i ↦ congruenceFormula (arities i) (Ks i) := by
  unfold setPlaceholderCongruence
  rw [Matrix.hom_conj, translateFormula_conj]
  congr 1
  funext i
  exact translate_setPlaceholderCongruenceSentence Ks i

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
/-- Internal provability of a finite conjunction, from provability of the
conjuncts. -/
lemma tconj {m : ℕ} (v : Fin m → Bootstrapping.Formula V ℒₛₑₜ)
    (H : ∀ i, T.internalize V ⊢ v i) :
    T.internalize V ⊢ Matrix.conj v := by
  induction m with
  | zero =>
      show T.internalize V ⊢ ⊤
      cl_prover
  | succ m ih =>
      rw [show Matrix.conj v = v 0 ⋏ Matrix.conj (Matrix.vecTail v) from rfl]
      have h0 := H 0
      have hs := ih (Matrix.vecTail v) fun i ↦ H i.succ
      cl_prover [h0, hs]

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
/-- **The translated congruence antecedent is internally provable**, given
the per-placeholder congruence laws (supplied by `congruenceProof₁` and its
higher-arity companions at the concrete arity tuples the compiler uses). -/
theorem translatedCongruenceProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (H : ∀ i, T.internalize V ⊢ congruenceFormula (arities i) (Ks i)) :
    T.internalize V ⊢
      translateFormula Ks
        (Rewriting.emb (setPlaceholderCongruence k arities) :
          Proposition (setTemplateLanguage k arities)) := by
  rw [translate_setPlaceholderCongruence]
  exact tconj T _ H

end translate

end main

end LeanProofs.ZFCinPA.SetCongruence
