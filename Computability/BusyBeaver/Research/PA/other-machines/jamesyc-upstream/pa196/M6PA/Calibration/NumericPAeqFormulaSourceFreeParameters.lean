module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaCoverage
public import M6PA.Calibration.NumericPAeqTermSourceFreeParameters
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def sourceFreeParameters (s param : V) : V :=
  parameters (NumericPAeqTerm.dropLast (nth param 0)) (nth (nth param 0) s ∷ nth param 1)
noncomputable def sourceFreeParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out s param. ∃ b f d last nf, !nthDef b param 0 ∧ !nthDef f param 1 ∧
    !NumericPAeqTerm.dropLastGraph d b ∧ !nthDef last b s ∧ !adjoinDef nf last f ∧ !parametersGraph out d nf”
theorem sourceFreeParameters_graph (out s param : V) :
    sourceFreeParametersGraph.val.Evalb ![out,s,param] ↔ out=sourceFreeParameters s param := by
  simp [sourceFreeParametersGraph,sourceFreeParameters,parameters_graph,Matrix.comp_vecCons'']
instance sourceFreeParameters_defined : 𝚺ᴬ₁-Function₂ (sourceFreeParameters : V → V → V) via sourceFreeParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! sourceFreeParameters_graph (v 0) (v 1) (v 2)
theorem sourceFreeParameters_valid {s n param : V} (h : ParametersValid (s+1) n param) :
    ParametersValid s n (sourceFreeParameters s param) := by
  simp only [ParametersValid,sourceFreeParameters,parameters_bound,parameters_free]
  exact ⟨NumericPAeqTerm.dropLast_valid h.1,by simp [h.1.nth (lt_add_one s),h.2]⟩
theorem sourceFreeParameters_equality {s n param i : V} (h : ParametersValid (s+1) n param) :
    equalityTermParameters (sourceFreeParameters s param) i=
      NumericPAeqTerm.sourceFreeParameters s (equalityTermParameters param i) := by
  simp only [equalityTermParameters,sourceFreeParameters,NumericPAeqTerm.sourceFreeParameters,
    parameters_bound,parameters_free,NumericPAeqTerm.parameters_bound,NumericPAeqTerm.parameters_free,
    NumericPAeqTerm.parameters_result,
    NumericPAeqTerm.dropLast_shiftTerms (NumericPAeqTerm.shiftTerms_isSemitermVec h.1),
    NumericPAeqTerm.dropLast_shiftTerms h.1,
    NumericPAeqTerm.shiftTerms_nth (NumericPAeqTerm.shiftTerms_isSemitermVec h.1) (lt_add_one s),
    NumericPAeqTerm.shiftTerms_nth h.1 (lt_add_one s),
    NumericPAeqTerm.shiftTerms_adjoin h.2 (h.1.nth (lt_add_one s)),
    NumericPAeqTerm.shiftTerms_adjoin (NumericPAeqTerm.shiftTerms_isSemitermVec h.2) (h.1.nth (lt_add_one s)).termBShift]
theorem sourceFreeParameters_binder {s n param : V} (h : ParametersValid (s+1) n param) :
    binderParameters (sourceFreeParameters s param)=
      sourceFreeParameters (s+1) (binderParameters param) := by
  have hn : NumericPAeqTerm.shiftTerms (nth param 0) ≠ 0 := by
    intro he
    have hh := NumericPAeqTerm.shiftTerms_length h.1
    rw [he] at hh
    simp at hh
  simp only [binderParameters,sourceFreeParameters,parameters_bound,parameters_free,
    NumericPAeqTerm.dropLast_adjoin,hn,ite_false,nth_adjoin_succ,
    NumericPAeqTerm.dropLast_shiftTerms h.1,NumericPAeqTerm.shiftTerms_nth h.1 (lt_add_one s),
    NumericPAeqTerm.shiftTerms_adjoin h.2 (h.1.nth (lt_add_one s))]
#print axioms sourceFreeParameters_defined
#print axioms sourceFreeParameters_valid
#print axioms sourceFreeParameters_equality
#print axioms sourceFreeParameters_binder
end M6.PA.NumericPAeqFormula

