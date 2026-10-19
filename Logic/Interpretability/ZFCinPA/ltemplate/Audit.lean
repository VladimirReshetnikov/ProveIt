import ZFCinPA.LTemplate

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.LTemplateFocusedAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SetPlaceholderQuotient

variable {k : ℕ} {arities : Fin k → ℕ}
local instance : Language.Mem (setTemplateLanguage k arities) :=
  ⟨Sum.inl Language.Set.Rel.mem⟩

#print axioms LeanProofs.ZFCinPA.LTemplate.equality_cases
#print axioms LeanProofs.ZFCinPA.LTemplate.congruenceProof_le3
#print axioms LeanProofs.ZFCinPA.LTemplate.translated_axiom
#print axioms LeanProofs.ZFCinPA.LTemplate.compileT
#print axioms LeanProofs.ZFCinPA.LTemplate.compileT_provable
#print axioms LeanProofs.ZFCinPA.LTemplate.reduct_standard
#print axioms LeanProofs.ZFCinPA.LTemplate.pure_models
#print axioms LeanProofs.ZFCinPA.LTemplate.sep_iff
#print axioms LeanProofs.ZFCinPA.LTemplate.repl_iff
#print axioms LeanProofs.ZFCinPA.LTemplate.templ_provable

example : 𝗘𝗤 (setTemplateLanguage k arities) ⪯ templTheory k arities :=
  inferInstance

example (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ 𝗘𝗤 (setTemplateLanguage k arities)) :
    σ ∈ FirstOrder.Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory) ∨
      ∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i :=
  equality_cases σ h

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a : ℕ) (ha : a ≤ 3) (K : Bootstrapping.Semiformula V ℒₛₑₜ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ SetCongruence.congruenceFormula a K :=
  congruenceProof_le3 a ha K

example (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) (h : σ ∈ templTheory k arities) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  translated_axiom harity Ks σ h

example (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templTheory k arities ⊢! σ) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  compileT harity Ks d

example (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templTheory k arities ⊢ σ) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  compileT_provable harity Ks d
end Internal

section Reduct
variable {M : Type*} [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

example : s.lMap (setHom k arities) = SetTheory.standardStructure M :=
  reduct_standard

example [Nonempty M] [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities] :
    M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := k) (arities := arities)

example [Nonempty M] [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 2) (f : ℕ → M)
    (htot : ∀ x : M, ∃! y, p.Eval ![x, y] f) (a : M) :
    ∃ img : M, ∀ y : M, y ∈ img ↔ ∃ x, x ∈ a ∧ p.Eval ![x, y] f :=
  repl_iff p f htot a
end Reduct

example {M : Type*} [Nonempty M] [SetStructure M]
    [Structure (setTemplateLanguage k arities) M]
    [Structure.Mem (setTemplateLanguage k arities) M]
    [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 1) (f : ℕ → M) (a : M) :
    ∃ b : M, ∀ y : M, y ∈ b ↔ y ∈ a ∧ p.Eval ![y] f :=
  sep_iff p f a

example (σ : Sentence (setTemplateLanguage k arities))
    (H : ∀ (M : Type) [Nonempty M] [SetStructure M]
      [Structure (setTemplateLanguage k arities) M]
      [Structure.Eq (setTemplateLanguage k arities) M]
      [Structure.Mem (setTemplateLanguage k arities) M]
      [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities],
      M↓[setTemplateLanguage k arities] ⊧ σ) :
    templTheory k arities ⊢ σ := templ_provable σ H

end LeanProofs.ZFCinPA.LTemplateFocusedAudit
