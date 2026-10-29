import ZFCinPA.LTemplate
import ZFCinPA.NativeTheory

set_option autoImplicit false
noncomputable section

/-!
# Template theories over the native theory

The `LTemplate` apparatus, rebuilt over `NativeSet.nativeTheory` with global
image collection (GIC) in place of Separation and Replacement:

* `gicBodySource p`: the GIC body for an enlarged two-variable matrix `p`,
  translating to `gicBody` (`translate_gicBodySource`);
* `nativeGicProof`: for every internal core `K`, open or not, an internal
  `nativeTheory`-proof of `gicBody K` (the closing axiom code is recognized by
  `GicR`, then specialized);
* `templN k arities`: lifted `nativeTheory`, the equality axioms of the
  enlarged language, and the GIC closure for every enlarged matrix;
* `translated_axiomN`/`compileN`: a fixed source derivation over `templN`
  becomes an internal `nativeTheory`-proof of its translation at every
  interpretation of the placeholders (arities at most `3`);
* semantics: the `ℒₛₑₜ` reduct of a model of `templN` is a model of
  `nativeTheory` (`pure_modelsN`), GIC holds for every enlarged matrix
  (`gic_iffN`), and `templ_provableN` is completeness.
-/

namespace LeanProofs.ZFCinPA.NTemplate

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.NativeSet
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
  have hv : ((gicSubst01Const : ℕ) : V) = (^#0 ∷ (^#1 ∷ 0)) := by
    rw [val_gicSubst01Const]
    simp
  rw [hv]
  apply Bootstrapping.subst_eq_self K.isSemiformula (by simp)
  intro i hi
  have hi' : i < (2 : V) := by simpa using hi
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi') with rfl | rfl <;> simp

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma union_class_iff (T U : SetTheory) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := by
  change (V ⊧/![p] (T.Δ₁ch ⋎ U.Δ₁ch).val) ↔
    (V ⊧/![p] T.Δ₁ch.val) ∨ (V ⊧/![p] U.Δ₁ch.val)
  rw [HierarchySymbol.Semiformula.val_or]
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]

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

theorem closedGic_mem_native (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    closeFormulaCode ℒₛₑₜ (gicBodyVal K.val) ∈ nativeTheory.Δ₁Class := by
  change _ ∈ ((𝗘𝗤 ℒₛₑₜ ∪ nativeFixed) ∪ gicTheory : SetTheory).Δ₁Class
  rw [union_class_iff]
  exact Or.inr ((gic_class_iff _).mpr (closedGic_recognized K))

theorem nativeGic_isProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Proof nativeTheory (openAxiomProofCode ℒₛₑₜ (gicBody K).val) (gicBody K).val := by
  apply openAxiomProofCode_isProof _ (gicBody K).isSemiformula
  rw [← gicBodyVal_eq K]
  exact closedGic_mem_native K

/-- **Every internal GIC body is an internal theorem of `nativeTheory`.** -/
noncomputable def nativeGicProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    nativeTheory.internalize V ⊢! gicBody K :=
  typedProofOfCode _ _ _ (nativeGic_isProof K)

noncomputable def gicProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    nativeTheory.internalize V ⊢!
      translateFormula Ks (Rewriting.emb (gicBodySource p).univCl) := by
  apply closeTemplate Ks _ (gicBodySource p)
  intro b
  rw [translate_gicBodySource]
  exact nativeGicProof _

noncomputable def liftedNProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) nativeTheory) :
    nativeTheory.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) := by
  apply TProof.byAxm
  rcases h with ⟨τ, hτ, rfl⟩
  rw [translateFormula_lMap_set_emb]
  exact (Bootstrapping.Δ₁Class.mem_iff'' (T := nativeTheory)).mpr hτ

end Internal

/-! ## The template theory -/

/-- The native template theory over `k` placeholders. -/
def templN (k : ℕ) (arities : Fin k → ℕ) : FirstOrder.Theory (setTemplateLanguage k arities) :=
  FirstOrder.Theory.lMap (setHom k arities) nativeTheory ∪
    ((𝗘𝗤 (setTemplateLanguage k arities)) ∪
      Set.range (fun p : Semiproposition (setTemplateLanguage k arities) 2 =>
        (gicBodySource (k := k) (arities := arities) p).univCl))

instance : 𝗘𝗤 (setTemplateLanguage k arities) ⪯ templN k arities :=
  LO.Entailment.WeakerThan.ofSubset (fun _ h => Or.inr (Or.inl h))

/-- An equality axiom of the enlarged language is a lifted native axiom or a
placeholder congruence law. -/
lemma equality_casesN (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ 𝗘𝗤 (setTemplateLanguage k arities)) :
    σ ∈ FirstOrder.Theory.lMap (setHom k arities) nativeTheory ∨
      ∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i := by
  cases h with
  | refl =>
      left
      refine ⟨Theory.Eq.refl ℒₛₑₜ, Or.inl (Or.inl Theory.eqAxiom.refl), ?_⟩
      simp [Theory.Eq.refl, FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | symm =>
      left
      refine ⟨Theory.Eq.symm ℒₛₑₜ, Or.inl (Or.inl Theory.eqAxiom.symm), ?_⟩
      simp [Theory.Eq.symm, FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | trans =>
      left
      refine ⟨Theory.Eq.trans ℒₛₑₜ, Or.inl (Or.inl Theory.eqAxiom.trans), ?_⟩
      simp [Theory.Eq.trans, FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | funcExt f =>
      rcases f with f | f
      · exact f.elim
      · exact f.elim
  | relExt r =>
      rcases r with r | ⟨i, hi⟩
      · left
        refine ⟨Theory.Eq.relExt r, Or.inl (Or.inl (Theory.eqAxiom.relExt r)), ?_⟩
        cases r <;> simp [Theory.Eq.relExt, Matrix.conj,
          FirstOrder.Semiformula.Operator.eq_def, Matrix.comp_vecCons', Function.comp_def,
          Matrix.vecTail, Matrix.constant_eq_singleton]
        all_goals rfl
      · subst hi
        exact Or.inr ⟨i, rfl⟩

section Compile

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The congruence law of a placeholder of arity at most `3`, in `nativeTheory`. -/
lemma congruenceProofN_le3 : ∀ (a : ℕ), a ≤ 3 → (K : Bootstrapping.Semiformula V ℒₛₑₜ a) →
    nativeTheory.internalize V ⊢ SetCongruence.congruenceFormula a K
  | 0, _, K => SetCongruence.congruenceProof₀ nativeTheory K
  | 1, _, K => SetCongruence.congruenceProof₁ nativeTheory K
  | 2, _, K => SetCongruence.congruenceProof₂ nativeTheory K
  | 3, _, K => SetCongruence.congruenceProof₃ nativeTheory K
  | n + 4, h, _ => absurd h (by omega)

/-- **Every source axiom has an internal `nativeTheory` proof.** -/
lemma translated_axiomN (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) (h : σ ∈ templN k arities) :
    nativeTheory.internalize V ⊢ translateFormula Ks (Rewriting.emb σ) := by
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
    nativeTheory.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  compileOpenTemplate Ks
    (fun b σ h => (translated_axiomN harity (shiftedPredicates Ks b) σ h).get) d

theorem compileN_provable (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templN k arities ⊢ σ) :
    nativeTheory.internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
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
      σ.Eval (s := SetTheory.standardStructure M) e ε := by
  rw [liftSet, Semiformula.eval_lMap, LTemplate.reduct_standard]

/-- The `ℒₛₑₜ` reduct of a model of `templN` is a model of `nativeTheory`. -/
lemma pure_modelsN [M↓[setTemplateLanguage k arities] ⊧* templN k arities] :
    M↓[ℒₛₑₜ] ⊧* nativeTheory := by
  have h : (s.lMap (setHom k arities)).toStruc ⊧* nativeTheory := by
    constructor
    intro p hp
    apply Semiformula.models_lMap.mp
    exact LO.FirstOrder.Theory.models M (templN k arities) (Or.inl ⟨p, hp, rfl⟩)
  simpa only [LTemplate.reduct_standard] using h

omit [Structure.Eq (setTemplateLanguage k arities) M] in
/-- Global image collection for every enlarged matrix. -/
lemma gic_iffN [M↓[setTemplateLanguage k arities] ⊧* templN k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 2) (f : ℕ → M) (a : M) :
    ∃ b : M, (∀ y, y ∈ b → ∃ x, p.Eval ![x, y] f) ∧
      (∀ x, x ∈ a → (∃ y, p.Eval ![x, y] f) → ∃ y, y ∈ b ∧ p.Eval ![x, y] f) := by
  have h := LO.FirstOrder.Theory.models M (templN k arities) (Or.inr (Or.inr ⟨p, rfl⟩))
  have h' : ∀ f : ℕ → M, ∀ a : M, ∃ b : M, (∀ y, y ∈ b → ∃ x, p.Eval ![x, y] f) ∧
      (∀ x, x ∈ a → (∃ y, p.Eval ![x, y] f) → ∃ y, y ∈ b ∧ p.Eval ![x, y] f) := by
    simpa [models_iff, gicBodySource] using h
  exact h' f a

end Semantics

/-- **Completeness for native template sentences.** -/
theorem templ_provableN (σ : Sentence (setTemplateLanguage k arities))
    (H : ∀ (M : Type) [Nonempty M] [SetStructure M]
      [Structure (setTemplateLanguage k arities) M]
      [Structure.Eq (setTemplateLanguage k arities) M]
      [Structure.Mem (setTemplateLanguage k arities) M]
      [M↓[setTemplateLanguage k arities] ⊧* templN k arities],
      M↓[setTemplateLanguage k arities] ⊧ σ) :
    templN k arities ⊢ σ := by
  apply LO.FirstOrder.Theory.Proof.complete.{0,0}
  apply consequence_iff_eq.{0,0}.mpr
  intro M _ s _ hT
  letI : SetStructure M := ⟨fun y x =>
    Structure.rel (L := setTemplateLanguage k arities) (Sum.inl Language.Set.Rel.mem) ![x, y]⟩
  letI : Structure.Mem (setTemplateLanguage k arities) M := ⟨fun _ _ => Iff.rfl⟩
  letI : M↓[setTemplateLanguage k arities] ⊧* templN k arities := hT
  exact H M

end LeanProofs.ZFCinPA.NTemplate
