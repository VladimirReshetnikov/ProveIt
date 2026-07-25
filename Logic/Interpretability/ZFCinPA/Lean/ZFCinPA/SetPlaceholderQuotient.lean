import ZFCinPA.SetPlaceholders
import Foundation.FirstOrder.Completeness

/-!
# Equality completion for set-placeholder proof templates

The source theory of the set-placeholder compiler is `𝗭𝗙𝗖` lifted through
the `ℒₛₑₜ` summand of `setTemplateLanguage k arities`.  It therefore
contains congruence axioms for `=` and `∈`, but not for the `k` opaque
placeholder relations.  This matters at a completeness boundary: an
arbitrary first-order prestructure may interpret equality by a nontrivial
equivalence relation which the placeholders fail to respect.

This module isolates the `k` missing relational congruence sentences
(`Theory.Eq.relExt` at each placeholder).  Once they hold, every equality
axiom of the expanded language holds — the function-extensionality axioms
are *vacuous*, since neither `ℒₛₑₜ` nor the placeholder summand has any
function symbol.  Quotienting by interpreted equality then produces an
elementarily equivalent model with genuine Lean equality, and completeness
yields a proof of any semantically valid sentence from the congruence
antecedent (`complete_underSetPlaceholderCongruence`).

Unlike the arithmetic counterpart
(`BoundedPAConsistency.ModelCodedPredicateEqualityQuotient`), no
ring-structure bookkeeping is involved: the semantic hypothesis quantifies
over bare `ℒₛₑₜ`-template structures with genuine equality, which is
exactly what a set-theoretic semantic argument needs.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetPlaceholderQuotient

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders

/-! ## The missing congruence sentences -/

/-- Coordinatewise congruence for the `i`-th placeholder relation.  The
standard equality axiom `relExt` universally quantifies two copies of every
coordinate and transports the relation from the first tuple to the second. -/
noncomputable def setPlaceholderCongruenceSentence
    (k : ℕ) (arities : Fin k → ℕ) (i : Fin k) :
    Sentence (setTemplateLanguage k arities) :=
  Theory.Eq.relExt (placeholderRel i)

/-- All `k` placeholder congruence laws as one conjunctive antecedent. -/
noncomputable def setPlaceholderCongruence (k : ℕ) (arities : Fin k → ℕ) :
    Sentence (setTemplateLanguage k arities) :=
  Matrix.conj fun i : Fin k ↦ setPlaceholderCongruenceSentence k arities i

section Models

variable {k : ℕ} {arities : Fin k → ℕ}

private abbrev L (k : ℕ) (arities : Fin k → ℕ) : Language :=
  setTemplateLanguage k arities

/-- A finite conjunction of sentences is satisfied iff each conjunct is. -/
private theorem models_conj_iff {L' : Language}
    {M : Type*} [Nonempty M] [Structure L' M]
    {n : ℕ} (v : Fin n → Sentence L') :
    M↓[L'] ⊧ Matrix.conj v ↔ ∀ i, M↓[L'] ⊧ v i := by
  induction n with
  | zero =>
      constructor
      · intro _ i
        exact i.elim0
      · intro _
        exact Semantics.Top.models_verum _
  | succ n ih =>
      rw [show Matrix.conj v = v 0 ⋏ Matrix.conj (Matrix.vecTail v) from rfl,
        Semantics.And.models_and, ih]
      constructor
      · rintro ⟨h0, hs⟩ i
        cases i using Fin.cases with
        | zero => exact h0
        | succ i => exact hs i
      · intro h
        exact ⟨h 0, fun i ↦ h i.succ⟩

/-- Satisfying the conjunctive antecedent is satisfying each conjunct. -/
theorem models_setPlaceholderCongruence_iff
    {M : Type*} [Nonempty M] [Structure (L k arities) M] :
    M↓[L k arities] ⊧ setPlaceholderCongruence k arities ↔
      ∀ i, M↓[L k arities] ⊧ setPlaceholderCongruenceSentence k arities i :=
  models_conj_iff _

/-- Lifted `𝗭𝗙𝗖` plus the placeholder congruence laws satisfies every
equality axiom of the placeholder-enlarged language.

The `funcExt` axioms hold vacuously: neither `ℒₛₑₜ` nor the placeholder
summand has function symbols.  The reflexivity, symmetry, transitivity, and
`ℒₛₑₜ`-relation congruence axioms transfer from the `ℒₛₑₜ` reduct, which
models `𝗘𝗤 ℒₛₑₜ ⊆ 𝗭𝗙𝗖`; the placeholder congruence axioms are exactly the
hypotheses. -/
theorem models_fullEquality
    {M : Type*} [Nonempty M] [Structure (L k arities) M]
    (hZFC : M↓[L k arities] ⊧* templateZFC k arities)
    (hcong : ∀ i, M↓[L k arities] ⊧
      setPlaceholderCongruenceSentence k arities i) :
    M↓[L k arities] ⊧* 𝗘𝗤 (L k arities) := by
  /- Reason semantically in the `ℒₛₑₜ` reduct.  This avoids normalizing
  mapped equality syntax and works for arbitrary prestructures. -/
  letI : Structure ℒₛₑₜ M :=
    (inferInstance : Structure (L k arities) M).lMap (setHom k arities)
  have hSetZFC : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖 : SetTheory) := by
    constructor
    intro σ hσ
    exact Semiformula.models_lMap.mp <| hZFC.models _ ⟨σ, hσ, rfl⟩
  letI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖 : SetTheory) := hSetZFC
  letI : M↓[ℒₛₑₜ] ⊧* 𝗘𝗤 ℒₛₑₜ := models_of_subtheory hSetZFC
  constructor
  intro σ hσ
  cases hσ with
  | refl =>
      simp [models_iff, Theory.Eq.refl]
      intro x
      change Structure.Eq.eqv ℒₛₑₜ x x
      exact Structure.Eq.eqv_refl (L := ℒₛₑₜ) x
  | symm =>
      simp [models_iff, Theory.Eq.symm]
      intro x y hxy
      change Structure.Eq.eqv ℒₛₑₜ x y at hxy
      change Structure.Eq.eqv ℒₛₑₜ y x
      exact Structure.Eq.eqv_symm (L := ℒₛₑₜ) hxy
  | trans =>
      simp [models_iff, Theory.Eq.trans]
      intro x y z hxy hyz
      change Structure.Eq.eqv ℒₛₑₜ x y at hxy
      change Structure.Eq.eqv ℒₛₑₜ y z at hyz
      change Structure.Eq.eqv ℒₛₑₜ x z
      exact Structure.Eq.eqv_trans (L := ℒₛₑₜ) hxy hyz
  | @funcExt m f =>
      rcases f with f | f
      · exact f.elim
      · exact f.elim
  | @relExt m r =>
      rcases r with r | r
      · simp [models_iff, Theory.Eq.relExt]
        intro v hv
        change ∀ i, Structure.Eq.eqv ℒₛₑₜ
          (v (Fin.addCast m i)) (v (i.addNat m)) at hv
        exact (Structure.Eq.eqv_relExt (L := ℒₛₑₜ) r hv).mp
      · obtain ⟨i, hi⟩ := r
        subst hi
        exact hcong i

set_option maxHeartbeats 800000 in
/-- **Completeness under the placeholder congruence antecedent.**  A
sentence valid in every template structure with genuine equality modeling
the lifted `𝗭𝗙𝗖` is provable from the conjunction of the placeholder
congruence laws.

The proof quotients an arbitrary prestructure by its interpreted equality
(`Structure.Eq.QuotEq`); the congruence hypotheses make the placeholder
relations descend, and the quotient is elementarily equivalent. -/
noncomputable def complete_underSetPlaceholderCongruence
    (σ : Sentence (L k arities))
    (H : ∀ (X : Type)
        [Nonempty X]
        [Structure (L k arities) X]
        [Structure.Eq (L k arities) X]
        [X↓[L k arities] ⊧* templateZFC k arities],
        X↓[L k arities] ⊧ σ) :
    templateZFC k arities ⊢!
      setPlaceholderCongruence k arities 🡒 σ :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun M _ _ hZFC ↦ by
    rw [Semantics.Imp.models_imply]
    intro hcong
    have hcong' : ∀ i, M↓[L k arities] ⊧
        setPlaceholderCongruenceSentence k arities i :=
      models_setPlaceholderCongruence_iff.mp hcong
    letI : M↓[L k arities] ⊧* 𝗘𝗤 (L k arities) :=
      models_fullEquality hZFC hcong'

    let Q := Structure.Eq.QuotEq (L k arities) M
    letI : Nonempty Q := Structure.Eq.QuotEq.inhabited
    letI : Structure (L k arities) Q := Structure.Eq.QuotEq.struc
    letI : Structure.Eq (L k arities) Q :=
      Structure.Eq.QuotEq.structureEq
    have quotientElementary : Q ≡ₑ[L k arities] M :=
      Structure.Eq.QuotEq.elementaryEquiv (L k arities) M
    letI : Q↓[L k arities] ⊧* templateZFC k arities :=
      quotientElementary.modelsTheory.mpr hZFC
    exact quotientElementary.models.mp (H Q)).get

end Models

end LeanProofs.ZFCinPA.SetPlaceholderQuotient
