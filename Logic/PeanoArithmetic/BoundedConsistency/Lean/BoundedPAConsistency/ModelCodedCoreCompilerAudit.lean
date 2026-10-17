import BoundedPAConsistency.ModelCodedCoreCompiler
open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler

#print axioms LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler.compileCore
#print axioms LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler.discharge
#print axioms LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler.compileTemplate
#print axioms LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler.compileTemplate_isProof

noncomputable section

private def p0 : Sentence (templateLanguage 0) := .rel (Sum.inr (PlaceholderRel.predicate (arity := 0))) ![]
private def emSource : (∅ : Theory (templateLanguage 0)) ⊢! (p0 ⋎ ∼p0) where
  axioms := []
  axioms_mem := by simp
  derivation := by
    change LO.FirstOrder.Derivation [(Rewriting.emb p0 : Proposition (templateLanguage 0)) ⋎ ∼Rewriting.emb p0]
    exact .or (LO.FirstOrder.Derivation.eta (Rewriting.emb p0))


section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity : ℕ}
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {Γ : List (Proposition (templateLanguage arity))} (d : LO.FirstOrder.Derivation Γ) :
    T ⊢!ᵈᵉʳ mapSeq S Γ := compileCore T d S
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {T₁ : Theory (templateLanguage arity)} {σ : Sentence (templateLanguage arity)}
    (d : T₁ ⊢! σ) (hA : ∀ ψ ∈ d.axioms, T ⊢! translateFormula S (Rewriting.emb ψ)) :
    T ⊢! translateFormula S (Rewriting.emb σ) := compileTemplate T S d hA
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {T₁ : Theory (templateLanguage arity)} {σ : Sentence (templateLanguage arity)}
    (d : T₁ ⊢! σ) (hA : ∀ ψ ∈ d.axioms, T ⊢! translateFormula S (Rewriting.emb ψ)) :
    Proof T.theory (compileTemplate T S d hA).val (translateFormula S (Rewriting.emb σ)).val :=
  compileTemplate_isProof T S d hA
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {Γ : List (Proposition (templateLanguage arity))} (d : LO.FirstOrder.Derivation Γ) :
    T ⊢!ᵈᵉʳ mapSeq S.shift Γ := compileCore T d S.shift
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Formula V ℒₒᵣ) :
    T ⊢! translateFormula S (Rewriting.emb (p0 ⋎ ∼p0)) :=
  compileTemplate T S emSource (by intro ψ hp; exact (List.not_mem_nil hp).elim)
example (T : InternalTheory V ℒₒᵣ) :
    T ⊢! translateFormula ((Bootstrapping.Semiterm.fvar 17 : Bootstrapping.Semiterm V ℒₒᵣ 0) ≐ .fvar 18)
      (Rewriting.emb (p0 ⋎ ∼p0)) :=
  compileTemplate T _ emSource (by intro ψ hp; exact (List.not_mem_nil hp).elim)
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) 1)
    (Γ : List (Proposition (templateLanguage arity)))
    (d : LO.FirstOrder.Derivation (p.free :: Γ⁺)) :
    T ⊢!ᵈᵉʳ mapSeq S ((∀⁰ p) :: Γ) := compileCore T (.all d) S
example (T : InternalTheory V ℒₒᵣ) (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (Γ A : List (Proposition (templateLanguage arity)))
    (hA : ∀ p ∈ A, T ⊢! translateFormula S p)
    (d : T ⊢!ᵈᵉʳ mapSeq S (Γ ++ A.map (∼·))) :
    T ⊢!ᵈᵉʳ mapSeq S Γ := discharge T S Γ A hA d
end

end
