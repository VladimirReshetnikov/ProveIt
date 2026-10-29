import ZFCinPA.SizedOpenTemplate
import ZFCinPA.LTemplate

/-!
# Bounded template axiom leaves: the lifted `𝗭𝗙` axioms

`sized_open_compile` takes, as hypothesis `hax`, a bounded internal derivation
of every translated axiom leaf of the fixed template derivation. This module
discharges the leaves that are lifted `𝗭𝗙` axioms, including the equality
axioms of the enlarged language that are not placeholder congruence laws
(`LTemplate.equality_cases`).

A lifted axiom `τ.lMap setHom` translates to the quotation `⌜τ⌝`
(`translateFormula_lMap_set_emb`), so a single `axm` rule derives it. Its code
is bounded through `translate_level`, which works for every source formula and
avoids evaluating the numeral `⌜τ⌝`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedTemplateAxioms

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.SetCodeLevels
open LeanProofs.ZFCinPA.TemplateTranslateLevel LeanProofs.ZFCinPA.SizedOpenTemplate
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler LeanProofs.ZFCinPA.SetPlaceholderQuotient

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

theorem singleton_formulaSet (φ : Bootstrapping.Formula V L) :
    IsFormulaSet L (insert φ.val (∅ : V)) := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact φ.isSemiformula
  · simp at hy

theorem singleton_le {x e : V} (hx : x < e) : insert x (∅ : V) ≤ Exp.exp e :=
  DerivableLe.seq_le le_rfl (DerivableLe.insert_lt hx (fun y hy => by simp at hy))

variable {k : ℕ} {arities : Fin k → ℕ}

/-- **A lifted `𝗭𝗙` axiom leaf, bounded.** At placeholders of level `u`, the
translation of a lifted axiom `σ` has a one-rule derivation below
`2^(1024·e)` as soon as `lvB (tA σ · (u+1)) < e`. -/
theorem lifted_axiom_le (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u) (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory)) {e : V} (he : 4 ≤ e)
    (hle : lvB ((tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) * (u + 1)) < e) :
    DerivableLe (𝗭𝗙 : SetTheory) (insert (translateFormula Ks (Rewriting.emb σ)).val (∅ : V))
      (Exp.exp (1024 * e)) := by
  have hx := translate_level (Rewriting.emb σ) u Ks hK
  refine DerivableLe.by_axm he (singleton_le (lt_of_le_of_lt hx hle)) (singleton_formulaSet _)
    (translateFormula Ks (Rewriting.emb σ)).val (by simp) ?_
  rcases h with ⟨τ, hτ, rfl⟩
  rw [translateFormula_lMap_set_emb]
  exact (Bootstrapping.Δ₁Class.mem_iff'' (T := (𝗭𝗙 : SetTheory))).mpr hτ

/-- The same leaf at every buffered placeholder `shiftedPredicates Ks b`,
`b ≤ B`, in the shape `sized_open_compile` consumes. -/
theorem lifted_axiom_buffered (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u) (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory)) {e : V} (he : 4 ≤ e) (B : ℕ)
    (hle : lvB ((tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) *
      (u + B + 1)) < e) :
    ∀ b ≤ B, DerivableLe (𝗭𝗙 : SetTheory)
      (insert (translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ)).val (∅ : V))
      (Exp.exp (1024 * e)) := by
  intro b hb
  refine lifted_axiom_le _ (shifted_level Ks hK b) σ h he (lt_of_le_of_lt (lvB_mono ?_) hle)
  have hbB : (b : V) ≤ B := by exact_mod_cast hb
  exact mul_le_mul le_rfl (_root_.add_le_add (_root_.add_le_add le_rfl hbB) le_rfl)
    (Arithmetic.zero_le _) (Arithmetic.zero_le _)

/-- Lifted axioms and the non-congruence equality axioms of the template theory. -/
theorem templ_lifted_or_congruence (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ LTemplate.templTheory k arities) :
    σ ∈ Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory) ∨
      (∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i) ∨
      (∃ p, σ = (OpenSchemaTemplates.sepBodySource (k := k) (arities := arities) p).univCl) ∨
      (∃ p, σ = (OpenSchemaTemplates.repBodySource (k := k) (arities := arities) p).univCl) := by
  rcases h with h | (h | (⟨p, rfl⟩ | ⟨p, rfl⟩))
  · exact Or.inl h
  · rcases LTemplate.equality_cases σ h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨p, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))

end LeanProofs.ZFCinPA.SizedTemplateAxioms
