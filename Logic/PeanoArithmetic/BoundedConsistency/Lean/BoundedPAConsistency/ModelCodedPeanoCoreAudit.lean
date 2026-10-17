import BoundedPAConsistency.ModelCodedPeanoCore
open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore

#print axioms LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore.liftedPeanoAxiomProof
#print axioms LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore.compilePeanoTemplateOpen
#print axioms LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore.compilePeanoTemplateOpen_isPAProof

noncomputable section
private def p0 : Sentence (templateLanguage 0) := .rel (Sum.inr .predicate) ![]
private def emSource : templatePeano 0 ⊢! (p0 ⋎ ∼p0) where
  axioms := []
  axioms_mem := by simp
  derivation := by
    change LO.FirstOrder.Derivation [(Rewriting.emb p0 : Proposition (templateLanguage 0)) ⋎ ∼Rewriting.emb p0]
    exact .or (LO.FirstOrder.Derivation.eta (Rewriting.emb p0))
section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity : ℕ}
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (σ : Sentence (templateLanguage arity)) (hσ : σ ∈ templatePeano arity) :
    Peano.internalize V ⊢! translateFormula S (Rewriting.emb σ) := liftedPeanoAxiomProof S σ hσ
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    Peano.internalize V ⊢! translateFormula S (Rewriting.emb σ) := compilePeanoTemplateOpen S d
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    Proof Peano (compilePeanoTemplateOpen S d).val (translateFormula S (Rewriting.emb σ)).val :=
  compilePeanoTemplateOpen_isPAProof S d
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    Peano.internalize V ⊢! translateFormula S.shift (Rewriting.emb σ) := compilePeanoTemplateOpen S.shift d
example : Peano.internalize V ⊢!
    translateFormula ((Bootstrapping.Semiterm.fvar 17 : Bootstrapping.Semiterm V ℒₒᵣ 0) ≐ .fvar 18)
      (Rewriting.emb (p0 ⋎ ∼p0)) := compilePeanoTemplateOpen _ emSource
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (τ : ArithmeticSentence) (hτ : τ ∈ Peano) :
    Peano.internalize V ⊢! translateFormula S
      (Rewriting.emb (τ.lMap (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity)))) :=
  liftedPeanoAxiomProof S _ ⟨τ, hτ, rfl⟩
end
end
