import ZFCinPA.LTemplate
import ZFCinPA.GicTemplateSyntax
import ZFCinPA.ModelCodedSchemaAxioms
import ZFCinPA.ValidatorSeedQTheory222

set_option autoImplicit false
noncomputable section

/-!
# Template theories over the native theory

The `LTemplate` apparatus, rebuilt over `ValidatorSeedQTheory222.qTheory` with global
image collection (GIC) in place of Separation and Replacement:

* `gicBodySource p`: the GIC body for an enlarged two-variable matrix `p`,
  translating to `gicBody` (`translate_gicBodySource`);
* `nativeGicProof`: for every internal core `K`, open or not, an internal
  `qTheory`-proof of `gicBody K` (the closing axiom code is recognized by
  `GicR`, then specialized);
* `templN k arities`: lifted `qTheory`, the equality axioms of the
  enlarged language, and the GIC closure for every enlarged matrix;
* `translated_axiomN`/`compileN`: a fixed source derivation over `templN`
  becomes an internal `qTheory`-proof of its translation at every
  interpretation of the placeholders (arities at most `3`);
* semantics: the `ℒₛₑₜ` reduct of a model of `templN` is a model of
  `qTheory` (`pure_modelsN`), GIC holds for every enlarged matrix
  (`gic_iffN`), and `templ_provableN` is completeness.
-/

namespace LeanProofs.ZFCinPA.QTemplate

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.ValidatorSeedQTheory222
open LeanProofs.ZFCinPA.SetPlaceholderQuotient

variable {k : ℕ} {arities : Fin k → ℕ}

local instance : Language.Mem (setTemplateLanguage k arities) := ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## The source GIC body -/

/-- The GIC body over the enlarged language. -/
def gicBodySource (ψ : Semiproposition (setTemplateLanguage k arities) 2) :
    Proposition (setTemplateLanguage k arities) :=
  GicTemplateSyntax.gicBodySource ψ

/-- `y ∈ b` (level 3; `y = #0`, `b = #1`). -/
def srcYB3 : Semiproposition (setTemplateLanguage k arities) 3 :=
  GicTemplateSyntax.srcYB3

/-- `x ∈ a` (level 3; `x = #0`, `a = #2`). -/
def srcXA3 : Semiproposition (setTemplateLanguage k arities) 3 :=
  GicTemplateSyntax.srcXA3

/-- `y ∈ b` (level 4; `y = #0`, `b = #2`). -/
def srcYB4 : Semiproposition (setTemplateLanguage k arities) 4 :=
  GicTemplateSyntax.srcYB4

lemma gicBodySource_eq (ψ : Semiproposition (setTemplateLanguage k arities) 2) :
    gicBodySource ψ =
      ∀⁰ ∃⁰ ((∀⁰ (srcYB3 🡒 ∃⁰ (ψ ⇜ ![(#0 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #1]))) ⋏
        (∀⁰ (srcXA3 🡒 ((∃⁰ (ψ ⇜ ![(#1 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #0])) 🡒
          ∃⁰ (srcYB4 ⋏ (ψ ⇜ ![(#1 : SyntacticSemiterm (setTemplateLanguage k arities) 4), #0])))))) := GicTemplateSyntax.gicBodySource_eq ψ

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
    translateFormula Ks (gicBodySource p) = gicBody (translateFormula Ks p) := GicTemplateSyntax.translate_gicBodySource Ks p

/-- The support substitution is the raw identity on the core. -/
lemma gic_core_subst_identity (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) K.val = K.val :=
  GicTemplateSyntax.gic_core_subst_identity K

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma union_class_iff (T U : SetTheory) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := ModelCodedSchemaAxioms.union_class_iff T U p

lemma gic_class_iff (p : V) : p ∈ gicTheory.Δ₁Class ↔ GicR p :=
  GicTemplateSyntax.gic_class_iff p

/-- The closing code of an open GIC body is recognized. -/
theorem closedGic_recognized (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    GicR (closeFormulaCode ℒₛₑₜ (gicBodyVal K.val)) :=
  GicTemplateSyntax.closedGic_recognized K

theorem closedGic_mem_native (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    closeFormulaCode ℒₛₑₜ (gicBodyVal K.val) ∈ qTheory.Δ₁Class := by
  change _ ∈ ((((𝗘𝗤 ℒₛₑₜ ∪ {ValidatorFullSeedTheory222.irreflexiveSentence}) ∪ gicTheory) ∪ {qAx} : SetTheory)).Δ₁Class
  rw [union_class_iff, union_class_iff]
  exact Or.inl (Or.inr ((gic_class_iff _).mpr (closedGic_recognized K)))

theorem nativeGic_isProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Proof qTheory (openAxiomProofCode ℒₛₑₜ (gicBody K).val) (gicBody K).val :=
  GicTemplateSyntax.gicIsProofOf qTheory K (closedGic_mem_native K)

/-- **Every internal GIC body is an internal theorem of `qTheory`.** -/
noncomputable def nativeGicProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    qTheory.internalize V ⊢! gicBody K :=
  typedProofOfCode _ _ _ (nativeGic_isProof K)

noncomputable def gicProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    qTheory.internalize V ⊢!
      translateFormula Ks (Rewriting.emb (gicBodySource p).univCl) :=
  GicTemplateSyntax.gicProofOf qTheory nativeGicProof Ks p

noncomputable def liftedNProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) qTheory) :
    qTheory.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  OpenSchemaTemplates.liftedTheoryProof qTheory Ks σ h

end Internal

/-! ## The template theory -/

/-- The native template theory over `k` placeholders. -/
def templN (k : ℕ) (arities : Fin k → ℕ) : FirstOrder.Theory (setTemplateLanguage k arities) :=
  FirstOrder.Theory.lMap (setHom k arities) qTheory ∪
    ((𝗘𝗤 (setTemplateLanguage k arities)) ∪
      Set.range (fun p : Semiproposition (setTemplateLanguage k arities) 2 =>
        (gicBodySource (k := k) (arities := arities) p).univCl))

instance : 𝗘𝗤 (setTemplateLanguage k arities) ⪯ templN k arities :=
  LO.Entailment.WeakerThan.ofSubset (fun _ h => Or.inr (Or.inl h))

/-- An equality axiom of the enlarged language is a lifted native axiom or a
placeholder congruence law. -/
lemma equality_casesN (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ 𝗘𝗤 (setTemplateLanguage k arities)) :
    σ ∈ FirstOrder.Theory.lMap (setHom k arities) qTheory ∨
      ∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i :=
  LTemplate.equality_cases_of_subset _ (fun _ hτ => Or.inl (Or.inl (Or.inl (hτ)))) σ h

section Compile

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The congruence law of a placeholder of arity at most `3`, in `qTheory`. -/
lemma congruenceProofN_le3 : ∀ (a : ℕ), a ≤ 3 → (K : Bootstrapping.Semiformula V ℒₛₑₜ a) →
    qTheory.internalize V ⊢ SetCongruence.congruenceFormula a K :=
  LTemplate.congruenceProof_le3_of_eq qTheory

/-- **Every source axiom has an internal `qTheory` proof.** -/
lemma translated_axiomN (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) (h : σ ∈ templN k arities) :
    qTheory.internalize V ⊢ translateFormula Ks (Rewriting.emb σ) := by
  rcases h with h | (h | ⟨p, rfl⟩)
  · exact ⟨liftedNProof Ks σ h⟩
  · rcases equality_casesN σ h with h | ⟨i, rfl⟩
    · exact ⟨liftedNProof Ks σ h⟩
    · rw [SetCongruence.translate_setPlaceholderCongruenceSentence]
      exact congruenceProofN_le3 (arities i) (harity i) (Ks i)
  · exact ⟨gicProof Ks p⟩

/-- **Template compilation over the native theory.** -/
noncomputable def compileN (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templN k arities ⊢! σ) :
    qTheory.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  compileOpenTemplate Ks
    (fun b σ h => (translated_axiomN harity (shiftedPredicates Ks b) σ h).get) d

theorem compileN_provable (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templN k arities ⊢ σ) :
    qTheory.internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  ⟨compileN harity Ks d.get⟩

end Compile

/-! ## Models of the native template theory -/

section Semantics

variable {M : Type*} [Nonempty M] [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

/-- Lifted `ℒₛₑₜ` formulas read in the `ℒₛₑₜ` reduct. -/
@[simp] lemma eval_liftSet {n : ℕ} (σ : SetTheorySemisentence n) (e : Fin n → M) (ε : Empty → M) :
    (liftSet (k := k) (arities := arities) σ).Eval e ε ↔
      σ.Eval (s := SetTheory.standardStructure M) e ε := LTemplate.eval_set_lMap σ e ε

/-- The `ℒₛₑₜ` reduct of a model of `templN` is a model of `qTheory`. -/
lemma pure_modelsN [M↓[setTemplateLanguage k arities] ⊧* templN k arities] :
    M↓[ℒₛₑₜ] ⊧* qTheory :=
  LTemplate.pure_models_of_subset qTheory (templN k arities) (fun _ hp => Or.inl hp)

omit [Structure.Eq (setTemplateLanguage k arities) M] in
/-- Global image collection for every enlarged matrix. -/
lemma gic_iffN [M↓[setTemplateLanguage k arities] ⊧* templN k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 2) (f : ℕ → M) (a : M) :
    ∃ b : M, (∀ y, y ∈ b → ∃ x, p.Eval ![x, y] f) ∧
      (∀ x, x ∈ a → (∃ y, p.Eval ![x, y] f) → ∃ y, y ∈ b ∧ p.Eval ![x, y] f) :=
  GicTemplateSyntax.gic_iff_of_mem (templN k arities) p (Or.inr (Or.inr ⟨p, rfl⟩)) f a

end Semantics

/-- **Completeness for native template sentences.** -/
theorem templ_provableN (σ : Sentence (setTemplateLanguage k arities))
    (H : ∀ (M : Type) [Nonempty M] [SetStructure M]
      [Structure (setTemplateLanguage k arities) M]
      [Structure.Eq (setTemplateLanguage k arities) M]
      [Structure.Mem (setTemplateLanguage k arities) M]
      [M↓[setTemplateLanguage k arities] ⊧* templN k arities],
      M↓[setTemplateLanguage k arities] ⊧ σ) :
    templN k arities ⊢ σ :=
  LTemplate.provable_of_standard_models (templN k arities) σ H

end LeanProofs.ZFCinPA.QTemplate
