module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaCoverage
@[expose] public section

/-! Concrete finite syntactic environments exist even for nonstandard source
arity and formula codes. They map every old variable to free variable zero;
this is only syntax coverage, not a proof that the variable denotes an ordinal. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem repeatedTermVector {n t : V} (ht : IsSemiterm language n t) (k : V) :
    IsSemitermVec language k n (repeatVec t k) := by
  refine ⟨⟨by simp,?_⟩,?_⟩
  · intro i hi
    rw [nth_repeatVec t k hi]
    exact ht.isUTerm
  · intro i hi
    rw [nth_repeatVec t k hi]
    exact ht.bv

noncomputable def constantParameters (s p : V) : V :=
  parameters (repeatVec (qqFvar 0) s) (repeatVec (qqFvar 0) p)
noncomputable def constantParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out s p. ∃ t b f, !qqFvarDef t 0 ∧ !repeatVecDef b t s ∧ !repeatVecDef f t p ∧
    !parametersGraph out b f”
theorem constantParameters_graph (out s p : V) :
    constantParametersGraph.val.Evalb ![out,s,p] ↔ out=constantParameters s p := by
  simp [constantParametersGraph,constantParameters,parameters_graph,Matrix.comp_vecCons'']
instance constantParameters_defined :
    𝚺ᴬ₁-Function₂ (constantParameters : V → V → V) via constantParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! constantParameters_graph (v 0) (v 1) (v 2)

theorem constantParameters_covered {s p : V}
    (hp : IsSemiformula Presentation.language s p) (n : V) :
    FormulaCovered s n (constantParameters s p) p := by
  refine ⟨?_,hp,?_⟩
  · simp only [ParametersValid,constantParameters,parameters_bound,parameters_free,len_repeatVec]
    exact ⟨repeatedTermVector (by simp) s,repeatedTermVector (by simp) p⟩
  · simp [constantParameters]

theorem formula_covered_exists {s p : V} (hp : IsSemiformula Presentation.language s p) (n : V) :
    ∃ param,FormulaCovered s n param p := ⟨constantParameters s p,constantParameters_covered hp n⟩

theorem constantParameters_bound_nth {s p i : V} (hi : i<s) :
    nth (nth (constantParameters s p) 0) i=qqFvar 0 := by
  simp [constantParameters,nth_repeatVec _ _ hi]
theorem constantParameters_free_nth {s p i : V} (hi : i<p) :
    nth (nth (constantParameters s p) 1) i=qqFvar 0 := by
  simp [constantParameters,nth_repeatVec _ _ hi]

#print axioms repeatedTermVector
#print axioms constantParameters_defined
#print axioms constantParameters_covered
#print axioms formula_covered_exists
#print axioms constantParameters_bound_nth
#print axioms constantParameters_free_nth
end M6.PA.NumericPAeqFormula

