module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateAtoms
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Bound quantification shifts the term environments, not the hole's free parameters. -/
noncomputable def bindBound (b : V) : V := qqBvar 0 ∷ NumericPAeqTerm.shiftTerms b
noncomputable def bindFree (f : V) : V := NumericPAeqTerm.shiftTerms f
noncomputable def bindBoundGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out b. ∃ bs z, !NumericPAeqTerm.shiftTermsGraph bs b ∧ !qqBvarDef z 0 ∧ !adjoinDef out z bs”
noncomputable def bindFreeGraph : 𝚺ᴬ₁.Semisentence 2 := NumericPAeqTerm.shiftTermsGraph
theorem bindBound_graph (out b : V) :
    bindBoundGraph.val.Evalb ![out,b] ↔ out=bindBound b := by
  simp [bindBoundGraph,bindBound,NumericPAeqTerm.shiftTerms_graph]
theorem bindFree_graph (out f : V) :
    bindFreeGraph.val.Evalb ![out,f] ↔ out=bindFree f :=
  NumericPAeqTerm.shiftTerms_graph out f
theorem bindEnvironments_valid {s n b f : V} (h : EnvironmentsValid s n b f) :
    EnvironmentsValid (s+1) (n+1) (bindBound b) (bindFree f) := by
  constructor
  · exact (NumericPAeqTerm.shiftTerms_isSemitermVec h.1).adjoin (by simp)
  · have hv := NumericPAeqTerm.shiftTerms_isSemitermVec h.2
    simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hv
#print axioms bindBound_graph
#print axioms bindFree_graph
#print axioms bindEnvironments_valid
end M6.PA.RelationalPredicateTemplate

