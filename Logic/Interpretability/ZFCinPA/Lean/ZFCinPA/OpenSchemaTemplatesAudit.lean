import ZFCinPA.OpenSchemaTemplates

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSchemaTemplates
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.OpenSchemaTemplates.translate_sepBodySource
#print axioms LeanProofs.ZFCinPA.OpenSchemaTemplates.translate_repBodySource
#print axioms LeanProofs.ZFCinPA.OpenSchemaTemplates.separationProof
#print axioms LeanProofs.ZFCinPA.OpenSchemaTemplates.replacementProof
#print axioms LeanProofs.ZFCinPA.OpenSchemaTemplates.liftedZFProof

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : Nat} {arities : Fin k → Nat}
variable (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))

example (p : Semiproposition (setTemplateLanguage k arities) 1) :
    translateFormula Ks (sepBodySource p) = sepBody (translateFormula Ks p) :=
  translate_sepBodySource Ks p

example (p : Semiproposition (setTemplateLanguage k arities) 2) :
    translateFormula Ks (repBodySource p) = repBody (translateFormula Ks p) :=
  translate_repBodySource Ks p

example (p : Semiproposition (setTemplateLanguage k arities) 1) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula Ks (Rewriting.emb (sepBodySource p).univCl) := separationProof Ks p

example (p : Semiproposition (setTemplateLanguage k arities) 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula Ks (Rewriting.emb (repBodySource p).univCl) := replacementProof Ks p

example (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  liftedZFProof Ks σ h
