import ZFCinPA.Instances
import ZFCinPA.FiniteTheoryRecognizer
import BoundedPAConsistency.InternalRelativization

/-!
# Represented relativization in the set language

`BoundedPAConsistency.InternalRelativization` proves, for any language, that
an internal theory `U` interprets an internal theory `T` relative to a domain
formula (`provable_relativize`, `provable_falsum_of_relativize`). One of its
hypotheses is that every closed internal term is a free variable. This module
discharges it for `ℒₛₑₜ`, which has no function symbols, in every model of
IΣ₁, so the interpretation theorem applies to set theories with only the
axiom and nonemptiness obligations left.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetRelativization

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- No internal code is a function symbol of `ℒₛₑₜ`. -/
lemma set_not_isFunc (k f : V) : ¬ (ℒₛₑₜ).IsFunc k f := by
  intro h
  have h' : V ⊧/![k, f] (instLORDefinableSet.func).val := h
  rw [show (instLORDefinableSet.func : 𝚺₀.Semisentence 2) = .mkSigma “k f. ⊥” from rfl] at h'
  simp at h'

/-- The internal set-language relation codes are binary equality or membership. -/
lemma set_isRel {k R : V} (hR : (ℒₛₑₜ).IsRel k R) : k = 2 ∧ (R = 0 ∨ R = 1) := by
  have hr' : V ⊧/![k, R] (LeanProofs.ZFCinPA.instLORDefinableSet.rel).val := hR
  rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.rel : 𝚺₀.Semisentence 2) =
    .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” from rfl] at hr'
  have hc : (k = 2 ∧ R = 0) ∨ (k = 2 ∧ R = 1) := by simpa using hr'
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, Or.inl h2⟩
  · exact ⟨h1, Or.inr h2⟩

open LO.FirstOrder.SetTheory

lemma finite_mem_ch_ofList {p : V} (l : List SetTheorySentence)
    (h : V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) : ∃ σ ∈ l, p=⌜σ⌝ :=
  (FiniteTheoryRecognizer.ofList_class_iff l p).mp h

lemma finite_mem_ch_ofFinite (T : SetTheory) (hT : Set.Finite T) {p : V}
    (h : V ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val) : ∃ σ ∈ T, p=⌜σ⌝ := by
  obtain ⟨σ,hσ,rfl⟩ := finite_mem_ch_ofList hT.toFinset.toList h
  exact ⟨σ,by simpa using hσ,rfl⟩

/-- **Every closed internal term of `ℒₛₑₜ` is a free variable.** -/
lemma isTerm_eq_fvar {t : V} (ht : IsTerm ℒₛₑₜ t) : ∃ j, t = ^&j :=
  IsSemiterm.induction 𝚺 (P := fun t : V => ∃ j, t = ^&j) (by definability)
    (fun z hz => absurd hz (by simp)) (fun x => ⟨x, rfl⟩)
    (fun k f _ hf _ _ => absurd hf (set_not_isFunc k f)) t ht

open LeanProofs.BoundedPAConsistency.InternalRelativization in
/-- **Internal relative interpretation of set theories.** In every model of
IΣ₁: if a set theory `U` proves `∃x δ(x)` and the relativization of every
axiom of `T` (with domain side formulas), then a `T`-refutation yields a
`U`-refutation, i.e. `Con(U) → Con(T)` holds internally. -/
theorem provable_falsum_of_relativize_set {T U : Theory ℒₛₑₜ} [T.Δ₁] [U.Δ₁] {d : V}
    (hd : IsSemiformula ℒₛₑₜ 1 d) (hds : shift ℒₛₑₜ d = d)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (relativize ℒₛₑₜ d p) (domSet ℒₛₑₜ d m)))
    (hne : Provable U (^∃ d)) (h : Provable T (^⊥ : V)) : Provable U (^⊥ : V) :=
  provable_falsum_of_relativize hd hds (fun _ ht => isTerm_eq_fvar ht) hAx hne h

end LeanProofs.ZFCinPA.SetRelativization
