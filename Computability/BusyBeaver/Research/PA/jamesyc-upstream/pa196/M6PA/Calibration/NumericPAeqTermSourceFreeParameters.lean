module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceFreeVectors
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem dropLast_shiftTerms {s n v : V} (h : IsSemitermVec language (s+1) n v) :
    dropLast (shiftTerms v)=shiftTerms (dropLast v) := by
  have hs := shiftTerms_isSemitermVec h
  apply nth_ext' s (dropLast_length hs.lh) (shiftTerms_length (dropLast_valid h))
  intro i hi
  rw [dropLast_nth hs.lh hi,shiftTerms_nth h (lt_trans hi (lt_add_one s)),
    shiftTerms_nth (dropLast_valid h) hi,dropLast_nth h.lh hi]

noncomputable def sourceFreeParameters (s param : V) : V :=
  parameters (dropLast (nth param 0)) (nth (nth param 0) s ∷ nth param 1) (nth param 2)
noncomputable def sourceFreeParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out s param. ∃ b f z d last nf, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧
    !dropLastGraph d b ∧ !nthDef last b s ∧ !adjoinDef nf last f ∧ !parametersGraph out d nf z”
theorem sourceFreeParameters_graph (out s param : V) :
    sourceFreeParametersGraph.val.Evalb ![out,s,param] ↔ out=sourceFreeParameters s param := by
  simp [sourceFreeParametersGraph,sourceFreeParameters,parameters_graph,Matrix.comp_vecCons'']
instance sourceFreeParameters_defined : 𝚺ᴬ₁-Function₂ (sourceFreeParameters : V→V→V) via sourceFreeParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! sourceFreeParameters_graph (v 0) (v 1) (v 2)

theorem sourceFreeParameters_valid {s n param : V} (h : ParametersValid (s+1) n param) :
    ParametersValid s n (sourceFreeParameters s param) := by
  simp only [ParametersValid,sourceFreeParameters,parameters_bound,parameters_free,parameters_result]
  exact ⟨dropLast_valid h.1,by simp [h.1.nth (lt_add_one s),h.2.1],h.2.2⟩

theorem sourceFreeParameters_child {s n param : V} (h : ParametersValid (s+1) n param) :
    childParameters (sourceFreeParameters s param)=sourceFreeParameters s (childParameters param) := by
  simp only [childParameters,sourceFreeParameters,parameters_bound,parameters_free,parameters_result,
    dropLast_shiftTerms h.1,shiftTerms_nth h.1 (lt_add_one s),
    shiftTerms_adjoin h.2.1 (h.1.nth (lt_add_one s))]

theorem sourceFreeParameters_binary {s n param i : V} (h : ParametersValid (s+1) n param) :
    binaryParameters (sourceFreeParameters s param) i=sourceFreeParameters s (binaryParameters param i) := by
  simp only [binaryParameters,sourceFreeParameters,parameters_bound,parameters_free,parameters_result,
    dropLast_shiftTerms (shiftTerms_isSemitermVec h.1),dropLast_shiftTerms h.1,
    shiftTerms_nth (shiftTerms_isSemitermVec h.1) (lt_add_one s),shiftTerms_nth h.1 (lt_add_one s),
    shiftTerms_adjoin h.2.1 (h.1.nth (lt_add_one s)),
    shiftTerms_adjoin (shiftTerms_isSemitermVec h.2.1) (h.1.nth (lt_add_one s)).termBShift]

#print axioms dropLast_shiftTerms
#print axioms sourceFreeParameters_graph
#print axioms sourceFreeParameters_defined
#print axioms sourceFreeParameters_valid
#print axioms sourceFreeParameters_child
#print axioms sourceFreeParameters_binary
end M6.PA.NumericPAeqTerm

