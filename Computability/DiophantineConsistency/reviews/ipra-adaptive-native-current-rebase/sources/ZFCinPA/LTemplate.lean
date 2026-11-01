import ZFCinPA.OpenSchemaTemplates
import ZFCinPA.SetCongruence
import ZFCinPA.SetPlaceholderQuotient

set_option autoImplicit false
noncomputable section

/-!
# Template theories for the constructible reflection generator

Every inductive step of the `hSchema` generator (design:
`Computability/BusyBeaver/Research/ZFC/pa_internalization.md`) is one fixed
sentence over `ℒₛₑₜ` enlarged by placeholder relations, proved once in Lean and
then compiled at internal formula codes by Codex's
`OpenSetTemplateCompiler.compileOpenTemplate`. This module supplies the shared
apparatus, following `CollectionTemplate254`/`CompiledCollection254` but with
the **full** separation and replacement schemata over the enlarged language:

* `templTheory k arities`: lifted `𝗭𝗙`, the equality axioms of the enlarged
  language, and `(sepBodySource p).univCl`, `(repBodySource p).univCl` for every
  enlarged matrix `p`;
* `translated_axiom`: every source axiom has an internal `𝗭𝗙` proof at every
  interpretation (lifted axioms by quotation, placeholder congruence by
  `SetCongruence.congruenceProof₀/₁/₂/₃`, schema instances by
  `OpenSchemaTemplates.separationProof/replacementProof`), for placeholder
  arities at most `3`;
* `compileT`: a fixed source derivation becomes an internal `𝗭𝗙` proof of its
  translation, nonstandard interpretations included;
* the semantic side: in a model of `templTheory` the `ℒₛₑₜ` reduct is a model
  of `𝗭𝗙` (`pure_models`), and Separation/Replacement hold for every enlarged
  matrix (`sep_iff`, `repl_iff`); `templ_provable` is completeness.
-/

namespace LeanProofs.ZFCinPA.LTemplate

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSchemaTemplates
open LeanProofs.ZFCinPA.SetPlaceholderQuotient

variable {k : ℕ} {arities : Fin k → ℕ}

/-- Membership of the enlarged language (the `ℒₛₑₜ` summand's symbol). -/
local instance : Language.Mem (setTemplateLanguage k arities) := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- Terms in the template language commute with subtype projection, because
that language has no function symbols. -/
theorem val_template_subtype {M ξ : Type*} {P : M → Prop}
    [Structure (setTemplateLanguage k arities) M]
    [Structure (setTemplateLanguage k arities) {x // P x}]
    {n : ℕ} (t : Semiterm (setTemplateLanguage k arities) ξ n)
    (b : Fin n → {x // P x}) (f : ξ → {x // P x}) :
    t.val (Subtype.val ∘ b) (Subtype.val ∘ f) = (t.val b f).1 := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func g v => rcases g with g | g <;> exact g.elim

/-- The template theory over `k` placeholders. -/
def templTheory (k : ℕ) (arities : Fin k → ℕ) : FirstOrder.Theory (setTemplateLanguage k arities) :=
  FirstOrder.Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory) ∪
    ((𝗘𝗤 (setTemplateLanguage k arities)) ∪
      (Set.range (fun p : Semiproposition (setTemplateLanguage k arities) 1 =>
          (sepBodySource (k := k) (arities := arities) p).univCl) ∪
        Set.range (fun p : Semiproposition (setTemplateLanguage k arities) 2 =>
          (repBodySource (k := k) (arities := arities) p).univCl)))

instance : 𝗘𝗤 (setTemplateLanguage k arities) ⪯ templTheory k arities :=
  LO.Entailment.WeakerThan.ofSubset (fun _ h => Or.inr (Or.inl h))

/-! ## Equality axioms -/

/-- An enlarged equality axiom lifts from a theory containing equality or is
a placeholder congruence law. -/
lemma equality_cases_of_subset (T : SetTheory) (hT : (𝗘𝗤 ℒₛₑₜ : SetTheory) ⊆ T)
    (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ 𝗘𝗤 (setTemplateLanguage k arities)) :
    σ ∈ FirstOrder.Theory.lMap (setHom k arities) T ∨
      ∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i := by
  cases h with
  | refl =>
      left
      refine ⟨Theory.Eq.refl ℒₛₑₜ,
        hT Theory.eqAxiom.refl, ?_⟩
      simp [Theory.Eq.refl, FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | symm =>
      left
      refine ⟨Theory.Eq.symm ℒₛₑₜ,
        hT Theory.eqAxiom.symm, ?_⟩
      simp [Theory.Eq.symm, FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | trans =>
      left
      refine ⟨Theory.Eq.trans ℒₛₑₜ,
        hT Theory.eqAxiom.trans, ?_⟩
      simp [Theory.Eq.trans, FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | funcExt f =>
      rcases f with f | f
      · exact f.elim
      · exact f.elim
  | relExt r =>
      rcases r with r | ⟨i, hi⟩
      · left
        refine ⟨Theory.Eq.relExt r,
          hT (Theory.eqAxiom.relExt r), ?_⟩
        cases r <;> simp [Theory.Eq.relExt, Matrix.conj,
          FirstOrder.Semiformula.Operator.eq_def, Matrix.comp_vecCons', Function.comp_def,
          Matrix.vecTail, Matrix.constant_eq_singleton]
        all_goals rfl
      · subst hi
        exact Or.inr ⟨i, rfl⟩

/-- Equality axioms are lifted ZF axioms or placeholder congruence laws. -/
lemma equality_cases (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ 𝗘𝗤 (setTemplateLanguage k arities)) :
    σ ∈ FirstOrder.Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory) ∨
      ∃ i : Fin k, σ = setPlaceholderCongruenceSentence k arities i :=
  equality_cases_of_subset 𝗭𝗙 (fun τ hτ => ZermeloFraenkel.axiom_of_equality τ hτ) σ h

/-! ## Translated axioms and compilation -/

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma embSubsts_app {n m : ℕ} (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n)
    (σ : Semisentence (setTemplateLanguage k arities) m) :
    (Rew.embSubsts v ▹ σ : Semiproposition (setTemplateLanguage k arities) n) =
      Rew.subst v ▹ (Rewriting.emb σ : Semiproposition (setTemplateLanguage k arities) m) := by
  have e : (Rew.embSubsts v : Rew (setTemplateLanguage k arities) Empty m ℕ n) =
      (Rew.subst v).comp Rew.emb := by
    ext x
    · simp [Rew.comp_app]
    · exact x.elim
  rw [e, TransitiveRewriting.comp_app]

/-- A translated lifted sentence under a substitution. -/
lemma translate_embSubsts_liftSet (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {n m : ℕ} (v : Fin m → SyntacticSemiterm (setTemplateLanguage k arities) n)
    (σ : SetTheorySemisentence m) :
    (translateFormula Ks (Rew.embSubsts v ▹ liftSet σ)).val =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ translateTerm (V := V) (v i)) (⌜σ⌝ : V) := by
  rw [embSubsts_app, translateFormula_subst, translateFormula_emb_liftSet,
    Bootstrapping.Semiformula.val_substs]
  rfl


/-- A theory containing equality proves congruence for arity at most `3`. -/
lemma congruenceProof_le3_of_eq (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T] : ∀ (a : ℕ), a ≤ 3 → (K : Bootstrapping.Semiformula V ℒₛₑₜ a) →
    T.internalize V ⊢ SetCongruence.congruenceFormula a K
  | 0, _, K => SetCongruence.congruenceProof₀ T K
  | 1, _, K => SetCongruence.congruenceProof₁ T K
  | 2, _, K => SetCongruence.congruenceProof₂ T K
  | 3, _, K => SetCongruence.congruenceProof₃ T K
  | n + 4, h, _ => absurd h (by omega)

lemma congruenceProof_le3 : ∀ (a : ℕ), a ≤ 3 → (K : Bootstrapping.Semiformula V ℒₛₑₜ a) →
    (𝗭𝗙 : SetTheory).internalize V ⊢ SetCongruence.congruenceFormula a K :=
  congruenceProof_le3_of_eq 𝗭𝗙

/-- **Every source axiom has an internal `𝗭𝗙` proof** at every interpretation. -/
lemma translated_axiom (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities)) (h : σ ∈ templTheory k arities) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) := by
  rcases h with h | (h | (⟨p, rfl⟩ | ⟨p, rfl⟩))
  · exact ⟨liftedZFProof Ks σ h⟩
  · rcases equality_cases σ h with h | ⟨i, rfl⟩
    · exact ⟨liftedZFProof Ks σ h⟩
    · rw [SetCongruence.translate_setPlaceholderCongruenceSentence]
      exact congruenceProof_le3 (arities i) (harity i) (Ks i)
  · exact ⟨separationProof Ks p⟩
  · exact ⟨replacementProof Ks p⟩

/-- **Template compilation**: a fixed source derivation over `templTheory`
becomes an internal `𝗭𝗙` proof of its translation at `Ks`. -/
noncomputable def compileT (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templTheory k arities ⊢! σ) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  compileOpenTemplate Ks
    (fun b σ h => (translated_axiom harity (shiftedPredicates Ks b) σ h).get) d

theorem compileT_provable (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {σ : Sentence (setTemplateLanguage k arities)} (d : templTheory k arities ⊢ σ) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  ⟨compileT harity Ks d.get⟩

/-! ## Models of the template theory -/

section Semantics

variable {M : Type*} [Nonempty M] [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

omit [Nonempty M] in
/-- Genuine equality and membership identify the `ℒₛₑₜ` reduct. -/
lemma reduct_standard :
    s.lMap (setHom k arities) = SetTheory.standardStructure M := by
  apply Structure.ext
  · funext n f
    exact f.elim
  · funext n r v
    cases r
    · change Structure.rel (L := setTemplateLanguage k arities)
        (Sum.inl Language.Set.Rel.eq) v = (v 0 = v 1)
      exact propext (Structure.eq_lang (L := setTemplateLanguage k arities) (M := M) (v := v))
    · change Structure.rel (L := setTemplateLanguage k arities)
        (Sum.inl Language.Set.Rel.mem) v = (v 0 ∈ v 1)
      exact propext (Structure.mem_lang (L := setTemplateLanguage k arities) (M := M) (v := v))

/-- A lifted set-language sentence evaluates in the standard reduct. -/
lemma eval_set_lMap {n : ℕ} (σ : SetTheorySemisentence n) (e : Fin n → M) (ε : Empty → M) :
    (σ.lMap (setHom k arities)).Eval e ε ↔
      σ.Eval (s := SetTheory.standardStructure M) e ε := by
  rw [Semiformula.eval_lMap, reduct_standard]

/-- A model of an enlarged theory models every theory lifted into it. -/
lemma pure_models_of_subset (T : SetTheory) (S : Theory (setTemplateLanguage k arities))
    [M↓[setTemplateLanguage k arities] ⊧* S]
    (hTS : Theory.lMap (setHom k arities) T ⊆ S) : M↓[ℒₛₑₜ] ⊧* T := by
  have h : (s.lMap (setHom k arities)).toStruc ⊧* T := by
    constructor
    intro p hp
    apply Semiformula.models_lMap.mp
    exact LO.FirstOrder.Theory.models M S (hTS ⟨p, hp, rfl⟩)
  simpa only [reduct_standard] using h

/-- The `ℒₛₑₜ` reduct of a model of the template theory is a model of `𝗭𝗙`. -/
lemma pure_models [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities] :
    M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) :=
  pure_models_of_subset 𝗭𝗙 (templTheory k arities) (fun _ hp => Or.inl hp)

omit [Structure.Eq (setTemplateLanguage k arities) M] in
/-- Separation for every enlarged matrix. -/
lemma sep_iff [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 1) (f : ℕ → M) (a : M) :
    ∃ b : M, ∀ y : M, y ∈ b ↔ y ∈ a ∧ p.Eval ![y] f := by
  have h := LO.FirstOrder.Theory.models M (templTheory k arities)
    (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
  have h' : ∀ f : ℕ → M, ∀ a : M, ∃ b : M, ∀ y : M, y ∈ b ↔ y ∈ a ∧ p.Eval ![y] f := by
    simpa [models_iff, sepBodySource] using h
  exact h' f a

/-- Replacement (globally total form) for every enlarged matrix. -/
lemma repl_iff [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities]
    (p : Semiproposition (setTemplateLanguage k arities) 2) (f : ℕ → M)
    (htot : ∀ x : M, ∃! y, p.Eval ![x, y] f) (a : M) :
    ∃ img : M, ∀ y : M, y ∈ img ↔ ∃ x, x ∈ a ∧ p.Eval ![x, y] f := by
  have h := LO.FirstOrder.Theory.models M (templTheory k arities)
    (Or.inr (Or.inr (Or.inr ⟨p, rfl⟩)))
  have h' : ∀ f : ℕ → M, (∀ x : M, ∃! y, p.Eval ![x, y] f) →
      ∀ a : M, ∃ img : M, ∀ y : M, y ∈ img ↔ ∃ x, x ∈ a ∧ p.Eval ![x, y] f := by
    simpa [models_iff, repBodySource] using h
  exact h' f htot a

end Semantics

/-- **Completeness for template sentences**: it suffices to check the sentence
in every model of the template theory whose equality is genuine. -/
theorem provable_of_standard_models (T : Theory (setTemplateLanguage k arities))
    [𝗘𝗤 (setTemplateLanguage k arities) ⪯ T]
    (σ : Sentence (setTemplateLanguage k arities))
    (H : ∀ (M : Type) [Nonempty M] [SetStructure M]
      [Structure (setTemplateLanguage k arities) M]
      [Structure.Eq (setTemplateLanguage k arities) M]
      [Structure.Mem (setTemplateLanguage k arities) M]
      [M↓[setTemplateLanguage k arities] ⊧* T],
      M↓[setTemplateLanguage k arities] ⊧ σ) :
    T ⊢ σ := by
  apply LO.FirstOrder.Theory.Proof.complete.{0,0}
  apply consequence_iff_eq.{0,0}.mpr
  intro M _ s _ hT
  letI : SetStructure M := ⟨fun y x =>
    Structure.rel (L := setTemplateLanguage k arities) (Sum.inl Language.Set.Rel.mem) ![x, y]⟩
  letI : Structure.Mem (setTemplateLanguage k arities) M := ⟨fun _ _ => Iff.rfl⟩
  letI : M↓[setTemplateLanguage k arities] ⊧* T := hT
  exact H M

/-- Completeness for template sentences with genuine equality and membership. -/
theorem templ_provable (σ : Sentence (setTemplateLanguage k arities))
    (H : ∀ (M : Type) [Nonempty M] [SetStructure M]
      [Structure (setTemplateLanguage k arities) M]
      [Structure.Eq (setTemplateLanguage k arities) M]
      [Structure.Mem (setTemplateLanguage k arities) M]
      [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities],
      M↓[setTemplateLanguage k arities] ⊧ σ) :
    templTheory k arities ⊢ σ :=
  provable_of_standard_models (templTheory k arities) σ H

end LeanProofs.ZFCinPA.LTemplate
