import BoundedPAConsistency.ModelCodedTemplateGraph

open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore
open LeanProofs.BoundedPAConsistency.ModelCodedTemplateGraph

#print axioms translateTerm_eq_quote
#print axioms argumentVectorCode_cast
#print axioms atomCode_cast
#print axioms negativeAtomCode_cast
#print axioms graph_eval
#print axioms value_defined
#print axioms value_defined_delta
#print axioms value_total
#print axioms value_eq_typed
#print axioms provabilitySentence_eval
#print axioms fixed_template_sentence_true
#print axioms isigma1_proves_fixed_template
#print axioms peano_proves_fixed_template

noncomputable section
variable {arity n k : Nat} {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

example (t : SyntacticSemiterm (templateLanguage arity) n) :
    translateTerm (V := V) t = (⌜eraseTerm t⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) :=
  translateTerm_eq_quote t

example (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) :
    (argumentVectorCode v : V) = SemitermVec.val (fun i => translateTerm (V := V) (v i)) :=
  argumentVectorCode_cast v

example : argumentVectorCode (arity := arity) (n := n) ![] = 0 := rfl

example (p : Semiproposition (templateLanguage arity) n) (y s : V) :
    (graph p).val.Evalb ![y, s] ↔ y = value p s := graph_eval p y s

example (p : Semiproposition (templateLanguage arity) n) :
    ∃! y : V, (graph p).val.Evalb ![y, 0] := value_total p 0

example (p : Semiproposition (templateLanguage arity) n) (s : V) :
    ∃! y, (graph p).val.Evalb ![y, s] := value_total p s

example (p : Semiproposition (templateLanguage arity) n) (y s : V) :
    (deltaGraph p).val.Evalb ![y, s] ↔ y = value p s := by simp

example (p : Semiproposition (templateLanguage arity) n)
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity) :
    value p S.val = (translateFormula S p).val := value_eq_typed p S

example (p : Semiproposition (templateLanguage 1) n) (i : V) :
    (graph p).val.Evalb ![(translateFormula ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ .fvar i) p).val,
      ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ .fvar i : Bootstrapping.Semiformula V ℒₒᵣ 1).val] := by
  rw [graph_eval]
  exact (value_eq_typed p _).symm

example (S : Bootstrapping.Semiformula V ℒₒᵣ 2) :
    value (.rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2)) ![.fvar 3, .bvar 0] :
      Semiproposition (templateLanguage 2) 1) S.val =
    (translateFormula S (.rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
      ![.fvar 3, .bvar 0] : Semiproposition (templateLanguage 2) 1)).val :=
  value_eq_typed _ S

example (S : Bootstrapping.Semiformula V ℒₒᵣ 2) :
    value (.nrel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2)) ![.fvar 5, .bvar 0] :
      Semiproposition (templateLanguage 2) 1) S.val =
    (translateFormula S (.nrel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
      ![.fvar 5, .bvar 0] : Semiproposition (templateLanguage 2) 1)).val :=
  value_eq_typed _ S

example (S : Bootstrapping.Formula V ℒₒᵣ) :
    value (.rel (Sum.inr .predicate) ![] : Proposition (templateLanguage 0)) S.val = S.val := by
  simpa [translateFormula] using
    value_eq_typed (.rel (Sum.inr .predicate) ![] : Proposition (templateLanguage 0)) S

example (S : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    value (∀⁰ ∃⁰ (.rel (Sum.inr .predicate) ![.bvar 1]) : Proposition (templateLanguage 1)) S.val =
    (translateFormula S (∀⁰ ∃⁰ (.rel (Sum.inr .predicate) ![.bvar 1]) :
      Proposition (templateLanguage 1))).val := value_eq_typed _ S

example (p : Proposition (templateLanguage arity)) :
    (provabilitySentence p).Evalb (M := V) ![] ↔
      ∀ s : V, IsSemiformula ℒₒᵣ (arity : V) s → Provable Peano (value p s) :=
  provabilitySentence_eval p

example {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    𝗜𝚺₁ ⊢ provabilitySentence (Rewriting.emb σ) := isigma1_proves_fixed_template d

example {σ : Sentence (templateLanguage arity)} (d : templatePeano arity ⊢! σ) :
    Peano ⊢ provabilitySentence (Rewriting.emb σ) := peano_proves_fixed_template d

private def p0 : Sentence (templateLanguage 0) := .rel (Sum.inr .predicate) ![]
private def emSource : templatePeano 0 ⊢! (p0 ⋎ ∼p0) where
  axioms := []
  axioms_mem := by simp
  derivation := by
    change LO.FirstOrder.Derivation [(Rewriting.emb p0 : Proposition (templateLanguage 0)) ⋎ ∼Rewriting.emb p0]
    exact .or (LO.FirstOrder.Derivation.eta (Rewriting.emb p0))

example : Peano ⊢ provabilitySentence (Rewriting.emb (p0 ⋎ ∼p0)) :=
  peano_proves_fixed_template emSource
