module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermParameters
public import M6PA.Calibration.NumericPAeqFormulaCalibration
@[expose] public section

/-! Two finite vectors of target relational term codes. A source quantifier
adds its actual target bound variable and shifts every older bound/free image.
No host infinite environment is used in these model-valued operations. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqTerm (shiftTerms shiftTermsGraph shiftTerms_graph shiftTerms_isSemitermVec
  shiftTerms_length shiftTerms_nth)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def parameters (b f : V) : V := b ∷ (f ∷ 0)
noncomputable def parametersGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out b f. ∃ fs, !adjoinDef fs f 0 ∧ !adjoinDef out b fs”
theorem parameters_graph (out b f : V) :
    parametersGraph.val.Evalb ![out,b,f] ↔ out=parameters b f := by
  simp [parametersGraph,parameters]
@[simp] theorem parameters_bound (b f : V) : nth (parameters b f) 0=b := by simp [parameters]
@[simp] theorem parameters_free (b f : V) : nth (parameters b f) 1=f := by simp [parameters]

noncomputable def binderParameters (param : V) : V :=
  parameters (qqBvar 0 ∷ shiftTerms (nth param 0)) (shiftTerms (nth param 1))
noncomputable def binderParametersGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f bs fs zero fresh,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧
    !qqBvarDef zero 0 ∧ !adjoinDef fresh zero bs ∧ !parametersGraph out fresh fs”
theorem binderParameters_graph (out param : V) :
    binderParametersGraph.val.Evalb ![out,param] ↔ out=binderParameters param := by
  simp [binderParametersGraph,binderParameters,shiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance binderParameters_defined : 𝚺ᴬ₁-Function₁ (binderParameters : V → V) via binderParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! binderParameters_graph (v 0) (v 1)
theorem binderParameters_total_unique (param : V) :
    ∃! out,binderParametersGraph.val.Evalb ![out,param] :=
  ⟨binderParameters param,(binderParameters_graph _ _).mpr rfl,
    fun _ h => (binderParameters_graph _ _).mp h⟩
@[simp] theorem binderParameters_parameters (b f : V) :
    binderParameters (parameters b f)=parameters (qqBvar 0 ∷ shiftTerms b) (shiftTerms f) := by
  simp [binderParameters]

def ParametersValid (sourceArity targetArity param : V) : Prop :=
  IsSemitermVec language sourceArity targetArity (nth param 0) ∧
  IsSemitermVec language (len (nth param 1)) targetArity (nth param 1)

theorem binderParameters_valid {s n param : V} (h : ParametersValid s n param) :
    ParametersValid (s+1) (n+1) (binderParameters param) := by
  unfold ParametersValid binderParameters
  simp only [parameters_bound,parameters_free]
  refine ⟨(shiftTerms_isSemitermVec h.1).adjoin (by simp),?_⟩
  simpa [shiftTerms_length h.2] using shiftTerms_isSemitermVec h.2

theorem binderParameters_bound_zero (param : V) :
    nth (nth (binderParameters param) 0) 0=qqBvar 0 := by simp [binderParameters]
theorem binderParameters_bound_succ {s n param i : V} (h : ParametersValid s n param) (hi : i<s) :
    nth (nth (binderParameters param) 0) (i+1)=termBShift language (nth (nth param 0) i) := by
  simpa [binderParameters] using shiftTerms_nth h.1 hi

theorem binderParameters_free_nth {s n param i : V} (h : ParametersValid s n param)
    (hi : i<len (nth param 1)) :
    nth (nth (binderParameters param) 1) i=termBShift language (nth (nth param 1) i) := by
  simpa [binderParameters] using shiftTerms_nth h.2 hi

#print axioms binderParameters_defined
#print axioms binderParameters_total_unique
#print axioms binderParameters_valid
#print axioms binderParameters_bound_zero
#print axioms binderParameters_bound_succ
#print axioms binderParameters_free_nth
end M6.PA.NumericPAeqFormula

