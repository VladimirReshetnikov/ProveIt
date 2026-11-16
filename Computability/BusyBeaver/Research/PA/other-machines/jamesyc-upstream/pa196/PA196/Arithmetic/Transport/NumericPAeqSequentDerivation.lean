module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentDerivationStep
public import PA196.Arithmetic.Transport.NumericPAeqSequentBudgetInvariant
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormula
open M6.PA.NumericPAeqFormula.Sequent


/-! Full-PA model-code induction for the unchanged ordinaryPAeq derivation
predicate. The conclusion retains its explicit proof-wide source term budget
and the complete free-domain antecedent. -/
namespace PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem ordinary_derivation_requested (d f : V)
    (hd : Derivation Presentation.ordinaryPAeq d) (hb : SourceProofBudget d f) :
    RequestedCertificate f (fstIdx d) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ d<n, Derivation Presentation.ordinaryPAeq d → ∀ f : V,
      SourceProofBudget d f → RequestedCertificate f (fstIdx d) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ d<n, Derivation Presentation.ordinaryPAeq d → ∀ f : V,
        SourceProofBudget d f → RequestedCertificate f (fstIdx d)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb budgetedDerivationInvariant,by trivial,?_⟩
      intro n
      simpa using (budgetedDerivationInvariant_semantics (V:=V) n).symm
    · intro d hd
      exact False.elim (by simpa using hd)
    · intro n ih d hd
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hd) with he | hlt
      · subst d
        exact ordinary_derivation_requested_step n ih
      · exact ih d hlt
  exact hall (d+1) d (lt_add_one d) hd f hb

attribute [local irreducible] sourceProofBudgetGraph requestedSequentFormula
noncomputable def ordinaryDerivationSentence : ArithmeticSentence :=
  “∀ d f s, !((derivation Presentation.ordinaryPAeq).sigma) d →
    !sourceProofBudgetGraph d f → !fstIdxDef s d → !requestedSequentFormula f s”

theorem pa_proves_ordinary_derivation : theory ⊢ ordinaryDerivationSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [ordinaryDerivationSentence,models_iff,sourceProofBudget_graph,
    requestedSequent_semantics,Matrix.comp_vecCons'',eq_comm]
  intro d f s hd hb he
  subst s
  exact ordinary_derivation_requested (V:=V) d f hd hb

#print axioms ordinary_derivation_requested
#print axioms pa_proves_ordinary_derivation
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent

