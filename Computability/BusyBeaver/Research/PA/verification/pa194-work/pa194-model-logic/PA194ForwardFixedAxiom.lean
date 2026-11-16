import PA194ForwardRootQuote
import PA194PAeqOrdinaryTheoryClass
import PA194OrdinaryAxiomSingleton
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher PA194PAeqBind
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixedList_class (l : List (Sentence PA194PAeq.language)) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) ↔
      ∃ σ ∈ l, p = (Encodable.encode σ : V) := by
  induction l with
  | nil =>
    change (V ⊧/![p] (⊥ : ArithmeticSemisentence 1)) ↔ _
    simp
  | cons σ l ih =>
    change (V ⊧/![p] ((Theory.Δ₁.singleton σ).ch ⋎ (Theory.Δ₁.ofList l).ch).val) ↔ _
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or]
    rw [ih]
    change ((V ⊧/![p] “x. x = ↑(Encodable.encode σ)”) ∨ _) ↔ _
    simp [numeral_eq_natCast]

theorem fixedTheory_class (p : V) : p ∈ PA194PAeq.targetFixedTheory.Δ₁Class ↔
    ∃ σ ∈ PA194PAeq.targetFixedSentences, p = (Encodable.encode σ : V) := by
  change (V ⊧/![p] (Theory.Δ₁.ofList PA194PAeq.targetFixedSentences).ch.val) ↔ _
  exact fixedList_class _ _

variable (T : Theory SourceL) [T.Δ₁]
theorem root_fixed_supplier (d p : V)
    (hsupply : ∀ σ ∈ PA194PAeq.targetFixedSentences,
      Provable T (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V))
    (hp : p ∈ PA194PAeq.targetFixedTheory.Δ₁Class)
    (hlen : p < len (nth (rootParameters d) 1)) :
    Provable T (translateFormula (rootParameters d) p) := by
  obtain ⟨σ,hσ,rfl⟩ := (fixedTheory_class p).mp hp
  have hquote : (⌜(Rewriting.emb σ : SourceFormula 0)⌝ : V) = (Encodable.encode σ : V) := by
    rw [←Sentence.quote_def,Sentence.quote_eq_encode]
  have heq := root_translate_quote (Rewriting.emb σ : SourceFormula 0) d (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq]
  exact hsupply σ hσ
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem root_theoryAxiom_of_fixed_and_induction (d : V)
    (hsupply : ∀ σ ∈ PA194PAeq.targetFixedSentences,
      Provable T (⌜formula (Rewriting.emb σ : SourceFormula 0)
        (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V))
    (hind : ∀ p : V, IsSemiformula PA194PAeq.language 1 p →
      closedInduction p < len (nth (rootParameters d) 1) →
      Provable T (translateFormula (rootParameters d) (closedInduction p))) :
    ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      axm s p < len (nth (rootParameters d) 1) →
      ∃ e, DerivationOf T e (translatedSequent (rootParameters d) s) := by
  apply ordinaryTheoryAxiom_of_fixed_and_induction T (rootParameters_valid d)
  · intro p _ hp hlen
    exact root_fixed_supplier T d p hsupply hp hlen
  · exact hind
#print axioms root_theoryAxiom_of_fixed_and_induction
#print axioms fixedList_class
#print axioms fixedTheory_class
#print axioms root_fixed_supplier
end generic
end PA194ForwardTyped
