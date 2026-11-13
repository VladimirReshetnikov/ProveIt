module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermUniqueness
@[expose] public section

/-! A total model function represented by the genuine unique table-witness
relation. Classical selection is uniquely characterized in every PA model;
this does not claim an extracted executable standard-number compiler. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def valueSyntax (param t : V) : V := by
  classical
  exact if ht : IsUTerm Presentation.language t then Classical.choose (valueWitness_exists t param ht) else 0

attribute [local irreducible] valueWitnessGraph
noncomputable def valueSyntaxGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param t. (!((isUTerm Presentation.language).sigma) t ∧ !valueWitnessGraph out param t) ∨
    (¬!((isUTerm Presentation.language).pi) t ∧ out=0)”

theorem valueSyntax_witness (param t : V) (ht : IsUTerm Presentation.language t) :
    ValueWitness param t (valueSyntax param t) := by
  simpa [valueSyntax,ht] using Classical.choose_spec (valueWitness_exists t param ht)
theorem valueSyntax_invalid (param t : V) (ht : ¬IsUTerm Presentation.language t) :
    valueSyntax param t=0 := by simp [valueSyntax,ht]
theorem valueSyntax_eq_of_witness {param t out : V} (ht : IsUTerm Presentation.language t)
    (ho : ValueWitness param t out) : valueSyntax param t=out :=
  valueWitness_unique t param _ out ht (valueSyntax_witness param t ht) ho

theorem valueSyntax_graph (out param t : V) :
    valueSyntaxGraph.val.Evalb ![out,param,t] ↔ out=valueSyntax param t := by
  simp only [valueSyntaxGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [valueWitness_graph,Matrix.comp_vecCons'']
  by_cases ht : IsUTerm Presentation.language t
  · simp only [ht,true_and,not_true_eq_false,false_and,or_false]
    constructor
    · intro ho; exact (valueSyntax_eq_of_witness ht ho).symm
    · rintro rfl; exact valueSyntax_witness param t ht
  · simp [ht,valueSyntax_invalid param t ht]

instance valueSyntax_defined : 𝚺ᴬ₁-Function₂ (valueSyntax : V → V → V) via valueSyntaxGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! valueSyntax_graph (v 0) (v 1) (v 2)
instance valueSyntax_definable : 𝚺ᴬ₁-Function₂ (valueSyntax : V → V → V) :=
  valueSyntax_defined.to_definable

theorem valueSyntax_total_unique (param t : V) :
    ∃! out, valueSyntaxGraph.val.Evalb ![out,param,t] := by
  refine ⟨valueSyntax param t,(valueSyntax_graph _ _ _).mpr rfl,?_⟩
  intro out h; exact (valueSyntax_graph _ _ _).mp h

@[simp] theorem valueSyntax_bvar (param i : V) :
    valueSyntax param (qqBvar i)=variableValue (nth param 2) (nth (nth param 0) i) :=
  valueSyntax_eq_of_witness (by simp) (witness_bvar param i)
@[simp] theorem valueSyntax_fvar (param i : V) :
    valueSyntax param (qqFvar i)=variableValue (nth param 2) (nth (nth param 1) i) :=
  valueSyntax_eq_of_witness (by simp) (witness_fvar param i)
@[simp] theorem valueSyntax_zero (param : V) :
    valueSyntax param (qqFunc 0 0 0)=zeroValue (nth param 2) :=
  valueSyntax_eq_of_witness (by simp) (witness_zero param)
theorem valueSyntax_successor (param u : V) (hu : IsUTerm Presentation.language u) :
    valueSyntax param (qqFunc 1 1 (u∷0))=
      successorValue (nth param 2) (valueSyntax (childParameters param) u) :=
  valueSyntax_eq_of_witness (by simp [hu]) (witness_successor (valueSyntax_witness _ _ hu))
theorem valueSyntax_addition (param u v : V)
    (hu : IsUTerm Presentation.language u) (hv : IsUTerm Presentation.language v) :
    valueSyntax param (qqFunc 2 2 (u∷(v∷0)))=
      additionValue (nth param 2) (valueSyntax (binaryParameters param 1) u)
        (valueSyntax (binaryParameters param 0) v) :=
  valueSyntax_eq_of_witness (by simp [hu,hv])
    (witness_addition (valueSyntax_witness _ _ hu) (valueSyntax_witness _ _ hv))
theorem valueSyntax_multiplication (param u v : V)
    (hu : IsUTerm Presentation.language u) (hv : IsUTerm Presentation.language v) :
    valueSyntax param (qqFunc 2 3 (u∷(v∷0)))=
      multiplicationValue (nth param 2) (valueSyntax (binaryParameters param 1) u)
        (valueSyntax (binaryParameters param 0) v) :=
  valueSyntax_eq_of_witness (by simp [hu,hv])
    (witness_multiplication (valueSyntax_witness _ _ hu) (valueSyntax_witness _ _ hv))

#print axioms valueSyntax_witness
#print axioms valueSyntax_invalid
#print axioms valueSyntax_eq_of_witness
#print axioms valueSyntax_graph
#print axioms valueSyntax_defined
#print axioms valueSyntax_total_unique
#print axioms valueSyntax_bvar
#print axioms valueSyntax_fvar
#print axioms valueSyntax_zero
#print axioms valueSyntax_successor
#print axioms valueSyntax_addition
#print axioms valueSyntax_multiplication
end M6.PA.NumericPAeqTerm

