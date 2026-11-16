module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentCode
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
@[expose] public section

/-! Full-PA validity of the HFS scan under explicit per-member supported
formula interpretation. Membership, not vector lookup, controls the fold. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

attribute [local irreducible] sequentScanGraph supportedCoverageGraph
noncomputable def scanValidityInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ param s arity sourceArity,
    (∀ p, p∈s → !supportedCoverageGraph sourceArity arity param p) →
    ∃ out, !sequentScanGraph out param s n ∧ !((isSemiformula language).sigma) arity out”

theorem scanValidity_invariant (n : V) : scanValidityInvariant.Evalb ![n] ↔
    ∀ param s arity sourceArity : V,
      (∀ p, p∈s → SupportedFormulaCovered sourceArity arity param p) →
      IsSemiformula language arity (sequentScan param s n) := by
  simp [scanValidityInvariant,supportedCoverage_graph,sequentScan_graph,Matrix.comp_vecCons'']

theorem sequentScan_valid (param s n arity sourceArity : V)
    (h : ∀ p, p∈s → SupportedFormulaCovered sourceArity arity param p) :
    IsSemiformula language arity (sequentScan param s n) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ param s arity sourceArity : V,
      (∀ p, p∈s → SupportedFormulaCovered sourceArity arity param p) →
      IsSemiformula language arity (sequentScan param s n) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ param s arity sourceArity : V,
        (∀ p, p∈s → SupportedFormulaCovered sourceArity arity param p) →
        IsSemiformula language arity (sequentScan param s n)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb scanValidityInvariant,by trivial,?_⟩
      intro n
      simpa using (scanValidity_invariant (V:=V) n).symm
    · intro param s arity sourceArity h
      rw [sequentScan_zero]
      simp
    · intro n ih param s arity sourceArity h
      by_cases hm : n∈s
      · rw [sequentScan_mem _ _ _ hm]
        exact IsSemiformula.or.mpr ⟨formulaSyntax_supported_isSemiformula (h n hm),
          ih param s arity sourceArity h⟩
      · rw [sequentScan_not_mem _ _ _ hm]
        exact ih param s arity sourceArity h
  exact hall n param s arity sourceArity h

theorem sequent_valid (param s arity sourceArity : V)
    (h : ∀ p, p∈s → SupportedFormulaCovered sourceArity arity param p) :
    IsSemiformula language arity (sequentCode param s) :=
  sequentScan_valid param s s arity sourceArity h

#print axioms scanValidity_invariant
#print axioms sequentScan_valid
#print axioms sequent_valid
end M6.PA.NumericPAeqFormula.Sequent

