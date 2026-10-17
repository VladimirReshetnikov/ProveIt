import BoundedPAConsistency.ModelCodedCoreCompiler

/-!
# Open-matrix specialization of standard lifted-PA proof templates

A standard finite proof over lifted PA is specialized at any internal matrix,
including matrices with free parameters. Lifted PA axioms do not contain the
placeholder, so their translations are ordinary quoted PA axioms regardless of
S. This supplies the finite root axiom proofs required by the core compiler.
No arbitrary internally coded source-proof translation is asserted.
-/
namespace LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore

open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity : ℕ}

/-- The axiom proof resource is independent of the inserted matrix's support. -/
noncomputable def liftedPeanoAxiomProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (σ : Sentence (templateLanguage arity)) (hσ : σ ∈ templatePeano arity) :
    Peano.internalize V ⊢! translateFormula S (Rewriting.emb σ) :=
  TProof.byAxm (by
    rcases hσ with ⟨τ, hτ, rfl⟩
    change translateFormula S
      (Rewriting.emb (τ.lMap (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity))) :
        Proposition (templateLanguage arity)) ∈' (Peano.internalize V).theory
    rw [translateFormula_lMap_add₁_emb]
    exact (Bootstrapping.Δ₁Class.mem_iff'' (T := Peano)).mpr hτ)

/-- No FVFree hypothesis on S: the source derivation is standard and finite. -/
noncomputable def compilePeanoTemplateOpen
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    Peano.internalize V ⊢! translateFormula S (Rewriting.emb σ) :=
  compileTemplate (Peano.internalize V) S d
    (fun ψ hψ => liftedPeanoAxiomProof S ψ (d.axioms_mem ψ hψ))

set_option backward.isDefEq.respectTransparency false in
theorem compilePeanoTemplateOpen_isPAProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    Proof Peano (compilePeanoTemplateOpen S d).val
      (translateFormula S (Rewriting.emb σ)).val := by
  simpa [Proof] using (compilePeanoTemplateOpen S d).derivationOf

end LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore
