module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceSubstValidity
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SubstitutionCovered (s r n param w t : V) : Prop :=
  ParametersValid r n param ∧ IsSemiterm Presentation.language s t ∧ t≤len (nth param 1) ∧
    IsSemitermVec Presentation.language s r w ∧ ∀ i<s, nth w i≤len (nth param 1)
noncomputable def substitutionCoverageGraph : ArithmeticSemisentence 6 :=
  “s r n param w t. ∃ b f z l, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧ !lenDef l f ∧
    !((isSemitermVec language).sigma) r n b ∧ !((isSemitermVec language).sigma) l n f ∧
    !((isSemiterm language).sigma) n z ∧ !((isSemiterm Presentation.language).sigma) s t ∧ t≤l ∧
    !((isSemitermVec Presentation.language).sigma) s r w ∧ ∀ i<s, ∀ v, !nthDef v w i → v≤l”
theorem substitutionCoverage_graph (s r n param w t : V) :
    substitutionCoverageGraph.Evalb ![s,r,n,param,w,t] ↔ SubstitutionCovered s r n param w t := by
  simp [substitutionCoverageGraph,SubstitutionCovered,ParametersValid,Matrix.comp_vecCons'',and_assoc]

theorem substitution_covered_nth {s r n param w t i : V}
    (h : SubstitutionCovered s r n param w t) (hi : i<s) : TermCovered r n param (nth w i) :=
  ⟨h.1,h.2.2.2.1.nth hi,h.2.2.2.2 i hi⟩
theorem substitution_covered_child {s r n param w t v : V}
    (h : SubstitutionCovered s r n param w t) (hv : IsSemiterm Presentation.language s v) (hr : v<t) :
    SubstitutionCovered s r (n+1) (childParameters param) w v := by
  refine ⟨childParameters_valid h.1,hv,?_,h.2.2.2.1,?_⟩
  · simpa only [childParameters,parameters_free,shiftTerms_length h.1.2.1] using le_trans hr.le h.2.2.1
  · simpa only [childParameters,parameters_free,shiftTerms_length h.1.2.1] using h.2.2.2.2
theorem substitution_covered_binary {s r n param w t v i : V}
    (h : SubstitutionCovered s r n param w t) (hv : IsSemiterm Presentation.language s v) (hr : v<t) (hi : i<2) :
    SubstitutionCovered s r ((n+1)+1) (binaryParameters param i) w v := by
  refine ⟨binaryParameters_valid h.1 hi,hv,?_,h.2.2.2.1,?_⟩
  · simpa only [binaryParameters,parameters_free,shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)] using le_trans hr.le h.2.2.1
  · simpa only [binaryParameters,parameters_free,shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)] using h.2.2.2.2
#print axioms substitutionCoverage_graph
#print axioms substitution_covered_nth
#print axioms substitution_covered_child
#print axioms substitution_covered_binary
end M6.PA.NumericPAeqTerm
