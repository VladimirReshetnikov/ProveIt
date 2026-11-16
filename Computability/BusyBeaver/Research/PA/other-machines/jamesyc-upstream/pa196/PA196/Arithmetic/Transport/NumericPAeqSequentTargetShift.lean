module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentFold
public import M6PA.Calibration.NumericPAeqFormulaSupportedTargetShift
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormula
open M6.PA.NumericPAeqFormula.Sequent


/-! Target shift commutes with a scan over the SAME HFS index set. This does
not identify the differently ordered scan over source setShift. -/
namespace PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem SupportedSet.targetShift {param s : V} (h : SupportedSet param s) :
    SupportedSet (targetShiftParameters param) s := by
  intro p hp
  have hc := h p hp
  refine ⟨targetShiftParameters_valid hc.1,hc.2.1,?_⟩
  simpa [targetShiftParameters,NumericPAeqTerm.targetShiftTerms_length hc.1.2] using hc.2.2

attribute [local irreducible] sequentScanGraph targetShiftParametersGraph shiftGraph
noncomputable def scanShiftGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param s n. ∃ shifted a b, !targetShiftParametersGraph shifted param ∧
    !sequentScanGraph a param s n ∧ !sequentScanGraph b shifted s n ∧ !(shiftGraph language) b a”

theorem scanShift_graph (param s n : V) : scanShiftGraph.val.Evalb ![param,s,n] ↔
    shift language (sequentScan param s n)=sequentScan (targetShiftParameters param) s n := by
  simp [scanShiftGraph,targetShiftParameters_graph,sequentScan_graph,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] scanShiftGraph supportedSetGraph
noncomputable def scanShiftInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ param s, !supportedSetGraph param s → !scanShiftGraph param s n”

theorem scanShift_invariant (n : V) : scanShiftInvariant.Evalb ![n] ↔
    ∀ param s : V, SupportedSet param s →
      shift language (sequentScan param s n)=sequentScan (targetShiftParameters param) s n := by
  simp [scanShiftInvariant,supportedSet_graph,scanShift_graph,Matrix.comp_vecCons'']

theorem sequentScan_targetShift (param s n : V) (h : SupportedSet param s) :
    shift language (sequentScan param s n)=sequentScan (targetShiftParameters param) s n := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ param s : V, SupportedSet param s →
      shift language (sequentScan param s n)=sequentScan (targetShiftParameters param) s n := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ param s : V, SupportedSet param s →
        shift language (sequentScan param s n)=sequentScan (targetShiftParameters param) s n) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb scanShiftInvariant,by trivial,?_⟩
      intro n
      simpa using (scanShift_invariant (V:=V) n).symm
    · intro param s h
      simp
    · intro n ih param s h
      by_cases hm : n∈s
      · rw [sequentScan_mem _ _ _ hm,sequentScan_mem _ _ _ hm,
          shift_or (h.member_valid hm) (h.scan_valid n),formulaSyntax_supported_targetShift (h n hm),ih param s h]
      · rw [sequentScan_not_mem _ _ _ hm,sequentScan_not_mem _ _ _ hm,ih param s h]
  exact hall n param s h

theorem sequent_targetShift (param s : V) (h : SupportedSet param s) :
    shift language (sequentCode param s)=sequentCode (targetShiftParameters param) s :=
  sequentScan_targetShift param s s h

#print axioms SupportedSet.targetShift
#print axioms scanShift_graph
#print axioms scanShift_invariant
#print axioms sequentScan_targetShift
#print axioms sequent_targetShift
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent

