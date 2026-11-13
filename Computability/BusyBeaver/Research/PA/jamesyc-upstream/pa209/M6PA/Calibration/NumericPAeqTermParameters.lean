module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermConstructors
@[expose] public section

/-! Finite vectors of target term codes, not native variable labels. The
existential value binder shifts both environments and uses bound result zero.
Source/target arities remain explicit validity conditions, outside the packet. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def shiftTerms (v : V) : V := termBShiftVec language (len v) v
noncomputable def shiftTermsGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out v. ∃ k, !lenDef k v ∧ !(termBShiftVecGraph language) out k v”
theorem shiftTerms_graph (out v : V) :
    shiftTermsGraph.val.Evalb ![out,v] ↔ out=shiftTerms v := by
  simp [shiftTermsGraph,shiftTerms]
instance shiftTerms_defined : 𝚺ᴬ₁-Function₁ (shiftTerms : V → V) via shiftTermsGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! shiftTerms_graph (v 0) (v 1)

theorem shiftTerms_length {k n v : V} (h : IsSemitermVec language k n v) :
    len (shiftTerms v)=k := by simp [shiftTerms, h.lh,h.isUTerm]
theorem shiftTerms_nth {k n v i : V} (h : IsSemitermVec language k n v) (hi : i<k) :
    nth (shiftTerms v) i=termBShift language (nth v i) := by
  simp [shiftTerms,h.lh,nth_termBShiftVec h.isUTerm hi]
theorem shiftTerms_isSemitermVec {k n v : V} (h : IsSemitermVec language k n v) :
    IsSemitermVec language k (n+1) (shiftTerms v) := by
  simpa [shiftTerms,h.lh] using h.termBShiftVec

noncomputable def parameters (b f z : V) : V := b ∷ (f ∷ (z ∷ 0))
noncomputable def parametersGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out b f z. ∃ zs fs, !adjoinDef zs z 0 ∧ !adjoinDef fs f zs ∧ !adjoinDef out b fs”
theorem parameters_graph (out b f z : V) :
    parametersGraph.val.Evalb ![out,b,f,z] ↔ out=parameters b f z := by
  simp [parametersGraph,parameters]
@[simp] theorem parameters_bound (b f z : V) : nth (parameters b f z) 0=b := by simp [parameters]
@[simp] theorem parameters_free (b f z : V) : nth (parameters b f z) 1=f := by simp [parameters]
@[simp] theorem parameters_result (b f z : V) : nth (parameters b f z) 2=z := by simp [parameters]

noncomputable def childParameters (param : V) : V :=
  parameters (shiftTerms (nth param 0)) (shiftTerms (nth param 1)) (qqBvar 0)
noncomputable def childParametersGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f bs fs z,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧
    !qqBvarDef z 0 ∧ !parametersGraph out bs fs z”
theorem childParameters_graph (out param : V) :
    childParametersGraph.val.Evalb ![out,param] ↔ out=childParameters param := by
  simp [childParametersGraph,childParameters,shiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance childParameters_defined : 𝚺ᴬ₁-Function₁ (childParameters : V → V) via childParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! childParameters_graph (v 0) (v 1)
theorem childParameters_total_unique (param : V) :
    ∃! out, childParametersGraph.val.Evalb ![out,param] := by
  refine ⟨childParameters param,(childParameters_graph _ _).mpr rfl,?_⟩
  intro out h; exact (childParameters_graph _ _).mp h
@[simp] theorem childParameters_parameters (b f z : V) :
    childParameters (parameters b f z)=parameters (shiftTerms b) (shiftTerms f) (qqBvar 0) := by
  simp [childParameters]

/-- Finite free-environment length is independent of source bound arity. -/
def ParametersValid (sourceArity targetArity param : V) : Prop :=
  IsSemitermVec language sourceArity targetArity (nth param 0) ∧
  IsSemitermVec language (len (nth param 1)) targetArity (nth param 1) ∧
  IsSemiterm language targetArity (nth param 2)

theorem childParameters_valid {s n param : V} (h : ParametersValid s n param) :
    ParametersValid s (n+1) (childParameters param) := by
  rcases h with ⟨hb,hf,hz⟩
  unfold ParametersValid childParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨shiftTerms_isSemitermVec hb,?_,by simp⟩
  simpa [shiftTerms_length hf] using shiftTerms_isSemitermVec hf

theorem childParameters_bound_nth {s n param i : V} (h : ParametersValid s n param) (hi : i<s) :
    nth (nth (childParameters param) 0) i=termBShift language (nth (nth param 0) i) := by
  simpa [childParameters] using shiftTerms_nth h.1 hi

theorem childParameters_free_nth {s n param i : V} (h : ParametersValid s n param)
    (hi : i<len (nth param 1)) :
    nth (nth (childParameters param) 1) i=termBShift language (nth (nth param 1) i) := by
  simpa [childParameters] using shiftTerms_nth h.2.1 hi

#print axioms shiftTerms_graph
#print axioms shiftTerms_defined
#print axioms shiftTerms_length
#print axioms shiftTerms_nth
#print axioms shiftTerms_isSemitermVec
#print axioms parameters_graph
#print axioms parameters_bound
#print axioms parameters_free
#print axioms parameters_result
#print axioms childParameters_graph
#print axioms childParameters_defined
#print axioms childParameters_total_unique
#print axioms childParameters_parameters
#print axioms childParameters_valid
#print axioms childParameters_bound_nth
#print axioms childParameters_free_nth
end M6.PA.NumericPAeqTerm

