import ZFCinPA.LTemplate
import ZFCinPA.NativeGicDelta1
import ZFCinPA.ModelCodedSchemaAxioms

set_option autoImplicit false
noncomputable section

/-! Common syntax and translation for global-image collection templates. -/

namespace LeanProofs.ZFCinPA.GicTemplateSyntax

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient

variable {k : ℕ} {arities : Fin k → ℕ}

local instance : Language.Mem (setTemplateLanguage k arities) := ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## The source GIC body -/

/-- The GIC body over the enlarged language. -/
def gicBodySource (ψ : Semiproposition (setTemplateLanguage k arities) 2) :
    Proposition (setTemplateLanguage k arities) :=
  “∀ a, ∃ b, (∀ y, (y ∈ b → ∃ x, !ψ x y)) ∧
    (∀ x, (x ∈ a → ((∃ y, !ψ x y) → ∃ y, (y ∈ b ∧ !ψ x y))))”

/-- `y ∈ b` (level 3; `y = #0`, `b = #1`). -/
def srcYB3 : Semiproposition (setTemplateLanguage k arities) 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- `x ∈ a` (level 3; `x = #0`, `a = #2`). -/
def srcXA3 : Semiproposition (setTemplateLanguage k arities) 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]

/-- `y ∈ b` (level 4; `y = #0`, `b = #2`). -/
def srcYB4 : Semiproposition (setTemplateLanguage k arities) 4 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]

lemma gicBodySource_eq (ψ : Semiproposition (setTemplateLanguage k arities) 2) :
    gicBodySource ψ =
      ∀⁰ ∃⁰ ((∀⁰ (srcYB3 🡒 ∃⁰ (ψ ⇜ ![(#0 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #1]))) ⋏
        (∀⁰ (srcXA3 🡒 ((∃⁰ (ψ ⇜ ![(#1 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #0])) 🡒
          ∃⁰ (srcYB4 ⋏ (ψ ⇜ ![(#1 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #0])))))) := by
  simp [gicBodySource, srcYB3, srcXA3, srcYB4, FirstOrder.Semiformula.Operator.mem_def]

/-! ## Internal proofs of the translated GIC instances -/

section Internal

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler LeanProofs.ZFCinPA.OpenTemplateClosure
open LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma translate_gicBodySource
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    translateFormula Ks (gicBodySource p) = gicBody (translateFormula Ks p) := by
  rw [gicBodySource_eq]
  simp only [translateFormula_neg', translateFormula,
    translateFormula_subst, gicBody, srcYB3, srcXA3, srcYB4, gicAtomYB3, gicAtomXA3, gicAtomYB4,
    FirstOrder.Semiformula.typed_quote_rel, Semiterm.typed_quote_bvar,
    translateTerm_bvar, Bootstrapping.Semiformula.imp_def, Matrix.comp_vecCons', Matrix.empty_eq]
  all_goals rfl


/-- The support substitution is the raw identity on the core. -/
lemma gic_core_subst_identity (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) K.val = K.val := by
  have h : ((gicSubst01Const : ℕ) : V) = (repSubst3Const : V) := by
    rw [val_gicSubst01Const, val_repSubst3Const]
  rw [h]
  exact ModelCodedSchemaAxioms.rep_core_subst_identity K

lemma gic_class_iff (p : V) : p ∈ gicTheory.Δ₁Class ↔ GicR p := by
  change (V ⊧/![p] gicCh.val) ↔ _
  simp

/-- The closing code of an open GIC body is recognized. -/
theorem closedGic_recognized (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    GicR (closeFormulaCode ℒₛₑₜ (gicBodyVal K.val)) := by
  apply closeFormulaCode_schemaRecognizer gicBodyVal K
  · rw [gicBodyVal_eq K]; exact (gicBody K).isSemiformula
  · have h := subst01_le_gicBodyVal K.val
    rw [gic_core_subst_identity K] at h
    exact h

noncomputable def gicProofOf (T : SetTheory) [T.Δ₁]
    (hGic : ∀ K : Bootstrapping.Semiformula V ℒₛₑₜ 2, T.internalize V ⊢! gicBody K)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    T.internalize V ⊢! translateFormula Ks (Rewriting.emb (gicBodySource p).univCl) := by
  apply closeTemplate Ks _ (gicBodySource p)
  intro b
  rw [translate_gicBodySource]
  exact hGic _
theorem gicIsProofOf (T : SetTheory) [T.Δ₁] (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (hK : closeFormulaCode ℒₛₑₜ (gicBodyVal K.val) ∈ T.Δ₁Class) :
    Proof T (openAxiomProofCode ℒₛₑₜ (gicBody K).val) (gicBody K).val := by
  apply openAxiomProofCode_isProof _ (gicBody K).isSemiformula
  rw [← gicBodyVal_eq K]
  exact hK

end Internal

section Semantics

variable {M : Type*} [Nonempty M] [SetStructure M]
variable [Structure (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

/-- A model of a closed GIC instance satisfies the corresponding matrix condition. -/
lemma gic_iff_of_mem (T : Theory (setTemplateLanguage k arities))
    [M↓[setTemplateLanguage k arities] ⊧* T]
    (p : Semiproposition (setTemplateLanguage k arities) 2)
    (hp : (gicBodySource p).univCl ∈ T) (f : ℕ → M) (a : M) :
    ∃ b : M, (∀ y, y ∈ b → ∃ x, p.Eval ![x, y] f) ∧
      (∀ x, x ∈ a → (∃ y, p.Eval ![x, y] f) → ∃ y, y ∈ b ∧ p.Eval ![x, y] f) := by
  have h := LO.FirstOrder.Theory.models M T hp
  have h' : ∀ f : ℕ → M, ∀ a : M, ∃ b : M, (∀ y, y ∈ b → ∃ x, p.Eval ![x, y] f) ∧
      (∀ x, x ∈ a → (∃ y, p.Eval ![x, y] f) → ∃ y, y ∈ b ∧ p.Eval ![x, y] f) := by
    simpa [models_iff, gicBodySource] using h
  exact h' f a

end Semantics

end LeanProofs.ZFCinPA.GicTemplateSyntax
