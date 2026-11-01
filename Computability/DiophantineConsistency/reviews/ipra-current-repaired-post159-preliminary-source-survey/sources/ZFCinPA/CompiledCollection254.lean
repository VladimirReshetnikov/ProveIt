import ZFCinPA.CollectionTemplate254
import ZFCinPA.OpenSchemaTemplates
import ZFCinPA.SetCongruence

set_option autoImplicit false
noncomputable section

/-!
Translate one fixed ordinary Collection derivation into internal ZF proofs
for arbitrary binary internal predicates, including their free parameters.
Every source axiom is discharged: pure ZF, expanded equality, and the three
explicit schema instances. This does not yet identify the decoder's G clause.
-/
namespace LeanProofs.ZFCinPA.CompiledCollection254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.CollectionTemplate254
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LeanProofs.ZFCinPA.OpenSchemaTemplates
open LeanProofs.ZFCinPA.SetCongruence
open LeanProofs.ZFCinPA.SetPlaceholderQuotient
open scoped LO.FirstOrder.Arithmetic

/-- In this particular language the only additional equality axiom is binary
predicate congruence. The pure equality axioms are actual lifted ZF axioms. -/
lemma equality_cases (σ : Sentence CollectionTemplate254.Lang)
    (h : σ ∈ 𝗘𝗤 CollectionTemplate254.Lang) :
    σ ∈ Theory.lMap hom (𝗭𝗙 : SetTheory) ∨ σ = predicateCongruence := by
  cases h with
  | refl =>
      left
      refine ⟨Theory.Eq.refl ℒₛₑₜ,
        ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.refl, ?_⟩
      simp [Theory.Eq.refl,FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | symm =>
      left
      refine ⟨Theory.Eq.symm ℒₛₑₜ,
        ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.symm, ?_⟩
      simp [Theory.Eq.symm,FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | trans =>
      left
      refine ⟨Theory.Eq.trans ℒₛₑₜ,
        ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.trans, ?_⟩
      simp [Theory.Eq.trans,FirstOrder.Semiformula.Operator.eq_def]
      rfl
  | funcExt f =>
      rcases f with f | f
      · exact f.elim
      · exact f.elim
  | relExt r =>
      rcases r with r | ⟨i,hi⟩
      · left
        refine ⟨Theory.Eq.relExt r,
          ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt r), ?_⟩
        cases r <;> simp [Theory.Eq.relExt,Matrix.conj,
          FirstOrder.Semiformula.Operator.eq_def,Matrix.comp_vecCons',Function.comp_def,
          Matrix.vecTail,Matrix.constant_eq_singleton]
        all_goals rfl
      · subst hi
        have hi0 : i = 0 := Fin.eq_zero i
        subst i
        exact Or.inr rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma translated_equality
    (Ks : (i : Fin 1) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence CollectionTemplate254.Lang)
    (h : σ ∈ 𝗘𝗤 CollectionTemplate254.Lang) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) := by
  rcases equality_cases σ h with h | rfl
  · exact ⟨liftedZFProof Ks σ h⟩
  · change (𝗭𝗙 : SetTheory).internalize V ⊢
      translateFormula Ks (Rewriting.emb (setPlaceholderCongruenceSentence 1 arities 0))
    rw [translate_setPlaceholderCongruenceSentence]
    exact congruenceProof₂ 𝗭𝗙 (Ks 0)

/-- This callback covers the actual source theory at every interpreted family;
there is no schematic axiom, congruence, or shift-invariance premise. -/
lemma translated_axiom
    (Ks : (i : Fin 1) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence CollectionTemplate254.Lang) (h : σ ∈ collectionTheory) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) := by
  rcases h with h | h | h
  · exact ⟨liftedZFProof Ks σ h⟩
  · exact translated_equality Ks σ h
  · have hs : σ = witnessSeparation ∨ σ = rankReplacement ∨ σ = outputSeparation := by
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
    rcases hs with rfl | rfl | rfl
    · exact ⟨separationProof Ks witnessMatrix⟩
    · exact ⟨replacementProof Ks totalLeastMatrix⟩
    · exact ⟨separationProof Ks outputMatrix⟩

/-- One actual internal proof obtained by translating a fixed ordinary proof.
The binary K is arbitrary internal syntax and may have arbitrary free labels. -/
noncomputable def collectionProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula (fun _ : Fin 1 => K) (Rewriting.emb collectionSentence) :=
  compileOpenTemplate (fun _ => K)
    (fun b σ h => (translated_axiom (shiftedPredicates (fun _ => K) b) σ h).get)
    collection_provable.get

theorem collectionProof_isProof (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙 : SetTheory) (collectionProof K).val
      (translateFormula (fun _ : Fin 1 => K) (Rewriting.emb collectionSentence)).val := by
  simpa [Proof,Theory.internalize] using (collectionProof K).derivationOf

end LeanProofs.ZFCinPA.CompiledCollection254
