import ZFCinPA.NTemplate

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.NTemplateFocusedAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.NativeSet
open LeanProofs.ZFCinPA.NTemplate LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
open LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms

variable {k : ℕ} {arities : Fin k → ℕ}
local instance : Language.Mem (setTemplateLanguage k arities) :=
  ⟨Sum.inl Language.Set.Rel.mem⟩

#print axioms LeanProofs.ZFCinPA.NTemplate.gicBodySource_eq
#print axioms LeanProofs.ZFCinPA.NTemplate.translate_gicBodySource
#print axioms LeanProofs.ZFCinPA.NTemplate.gic_core_subst_identity
#print axioms LeanProofs.ZFCinPA.NTemplate.union_class_iff
#print axioms LeanProofs.ZFCinPA.NTemplate.gic_class_iff
#print axioms LeanProofs.ZFCinPA.NTemplate.closedGic_recognized
#print axioms LeanProofs.ZFCinPA.NTemplate.closedGic_mem_native
#print axioms LeanProofs.ZFCinPA.NTemplate.nativeGic_isProof
#print axioms LeanProofs.ZFCinPA.NTemplate.nativeGicProof
#print axioms LeanProofs.ZFCinPA.NTemplate.gicProof
#print axioms LeanProofs.ZFCinPA.NTemplate.liftedNProof
#print axioms LeanProofs.ZFCinPA.NTemplate.equality_casesN
#print axioms LeanProofs.ZFCinPA.NTemplate.congruenceProofN_le3
#print axioms LeanProofs.ZFCinPA.NTemplate.translated_axiomN
#print axioms LeanProofs.ZFCinPA.NTemplate.compileN
#print axioms LeanProofs.ZFCinPA.NTemplate.compileN_provable
#print axioms LeanProofs.ZFCinPA.NTemplate.eval_liftSet
#print axioms LeanProofs.ZFCinPA.NTemplate.pure_modelsN
#print axioms LeanProofs.ZFCinPA.NTemplate.gic_iffN
#print axioms LeanProofs.ZFCinPA.NTemplate.templ_provableN

example : 𝗘𝗤 (setTemplateLanguage k arities) ⪯ templN k arities := inferInstance

example (ψ : Semiproposition (setTemplateLanguage k arities) 2) :
    gicBodySource ψ =
      ∀⁰ ∃⁰ ((∀⁰ (srcYB3 🡒 ∃⁰ (ψ ⇜ ![(#0 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #1]))) ⋏
        (∀⁰ (srcXA3 🡒 ((∃⁰ (ψ ⇜ ![(#1 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #0])) 🡒
          ∃⁰ (srcYB4 ⋏ (ψ ⇜ ![(#1 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #0])))))) :=
  gicBodySource_eq ψ

example (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ 𝗘𝗤 (setTemplateLanguage k arities)) :
    σ ∈ FirstOrder.Theory.lMap (setHom k arities) nativeTheory ∨
      ∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i :=
  equality_casesN σ h

example {V : Type*} [ORingStructure V] (T U : SetTheory) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class :=
  union_class_iff T U p

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    translateFormula Ks (gicBodySource p) = gicBody (translateFormula Ks p) :=
  translate_gicBodySource Ks p

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) K.val = K.val :=
  gic_core_subst_identity K

example (p : V) : p ∈ gicTheory.Δ₁Class ↔ GicR p := gic_class_iff p

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    GicR (closeFormulaCode ℒₛₑₜ (gicBodyVal K.val)) := closedGic_recognized K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    closeFormulaCode ℒₛₑₜ (gicBodyVal K.val) ∈ nativeTheory.Δ₁Class :=
  closedGic_mem_native K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Proof nativeTheory (openAxiomProofCode ℒₛₑₜ (gicBody K).val) (gicBody K).val :=
  nativeGic_isProof K

example (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    nativeTheory.internalize V ⊢! gicBody K := nativeGicProof K

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    nativeTheory.internalize V ⊢!
      translateFormula Ks (Rewriting.emb (gicBodySource p).univCl) :=
  gicProof Ks p

example (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ FirstOrder.Theory.lMap (setHom k arities) nativeTheory) :
    nativeTheory.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  liftedNProof Ks σ h

example (a : ℕ) (ha : a ≤ 3) (K : Bootstrapping.Semiformula V ℒₛₑₜ a) :
    nativeTheory.internalize V ⊢ SetCongruence.congruenceFormula a K :=
  congruenceProofN_le3 a ha K

example (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) (h : σ ∈ templN k arities) :
    nativeTheory.internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  translated_axiomN harity Ks σ h

example (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templN k arities ⊢! σ) :
    nativeTheory.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  compileN harity Ks d

example (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templN k arities ⊢ σ) :
    nativeTheory.internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  compileN_provable harity Ks d
end Internal

section Semantics
variable {M : Type*} [Nonempty M] [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

example {n : ℕ} (σ : SetTheorySemisentence n) (e : Fin n → M) (ε : Empty → M) :
    (liftSet (k := k) (arities := arities) σ).Eval e ε ↔
      σ.Eval (s := SetTheory.standardStructure M) e ε :=
  eval_liftSet σ e ε

example [M↓[setTemplateLanguage k arities] ⊧* templN k arities] :
    M↓[ℒₛₑₜ] ⊧* nativeTheory := pure_modelsN (k := k) (arities := arities)
end Semantics

example {M : Type*} [Nonempty M] [SetStructure M]
    [Structure (setTemplateLanguage k arities) M]
    [Structure.Mem (setTemplateLanguage k arities) M]
    [M↓[setTemplateLanguage k arities] ⊧* templN k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 2) (f : ℕ → M) (a : M) :
    ∃ b : M, (∀ y, y ∈ b → ∃ x, p.Eval ![x, y] f) ∧
      (∀ x, x ∈ a → (∃ y, p.Eval ![x, y] f) → ∃ y, y ∈ b ∧ p.Eval ![x, y] f) :=
  gic_iffN p f a

example (σ : Sentence (setTemplateLanguage k arities))
    (H : ∀ (M : Type) [Nonempty M] [SetStructure M]
      [Structure (setTemplateLanguage k arities) M]
      [Structure.Eq (setTemplateLanguage k arities) M]
      [Structure.Mem (setTemplateLanguage k arities) M]
      [M↓[setTemplateLanguage k arities] ⊧* templN k arities],
      M↓[setTemplateLanguage k arities] ⊧ σ) :
    templN k arities ⊢ σ := templ_provableN σ H

end LeanProofs.ZFCinPA.NTemplateFocusedAudit
