module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaConstruction
@[expose] public section

/-! A genuine total Sigma-one arithmetic-to-relational formula syntax graph.
This requires PA models, preserves the exact interpretation constructors, and
has explicit invalid-source default zero. Validity and proof transport are
separate obligations; no function-valued recursion premise is assumed. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def formulaSyntax (param p : V) : V :=
  formulaConstruction.result Presentation.language param p
noncomputable def formulaSyntaxGraph : 𝚺ᴬ₁.Semisentence 3 :=
  formulaBlueprint.result Presentation.language
instance formulaSyntax_defined :
    𝚺ᴬ₁-Function₂ (formulaSyntax : V → V → V) via formulaSyntaxGraph :=
  formulaConstruction.result_defined (L := Presentation.language)

theorem formulaSyntax_graph (out param p : V) :
    formulaSyntaxGraph.val.Evalb ![out,param,p] ↔ out=formulaSyntax param p :=
  formulaSyntax_defined.defined ![out,param,p]
theorem formulaSyntax_total_unique (param p : V) :
    ∃! out,formulaSyntaxGraph.val.Evalb ![out,param,p] :=
  ⟨formulaSyntax param p,(formulaSyntax_graph _ _ _).mpr rfl,
    fun _ h => (formulaSyntax_graph _ _ _).mp h⟩
theorem formulaSyntax_invalid (param p : V) (h : ¬IsUFormula Presentation.language p) :
    formulaSyntax param p=0 :=
  formulaConstruction.result_prop_not (L := Presentation.language) param h

theorem formulaSyntax_rel (param k r ts : V) (hr : Presentation.language.IsRel k r)
    (ht : IsUTermVec Presentation.language k ts) :
    formulaSyntax param (qqRel k r ts)=atomCode param k r ts :=
  formulaConstruction.result_rel (L := Presentation.language) (param := param) hr ht

theorem formulaSyntax_nrel (param k r ts : V) (hr : Presentation.language.IsRel k r)
    (ht : IsUTermVec Presentation.language k ts) :
    formulaSyntax param (qqNRel k r ts)=neg RelationalSource.language (atomCode param k r ts) :=
  formulaConstruction.result_nrel (L := Presentation.language) (param := param) hr ht

theorem formulaSyntax_verum (param : V) : formulaSyntax param qqVerum=qqVerum :=
  formulaConstruction.result_verum (L := Presentation.language) (param := param)
theorem formulaSyntax_falsum (param : V) : formulaSyntax param qqFalsum=qqFalsum :=
  formulaConstruction.result_falsum (L := Presentation.language) (param := param)

theorem formulaSyntax_and (param p q : V)
    (hp : IsUFormula Presentation.language p) (hq : IsUFormula Presentation.language q) :
    formulaSyntax param (qqAnd p q)=qqAnd (formulaSyntax param p) (formulaSyntax param q) :=
  formulaConstruction.result_and (L := Presentation.language) (param := param) hp hq

theorem formulaSyntax_or (param p q : V)
    (hp : IsUFormula Presentation.language p) (hq : IsUFormula Presentation.language q) :
    formulaSyntax param (qqOr p q)=qqOr (formulaSyntax param p) (formulaSyntax param q) :=
  formulaConstruction.result_or (L := Presentation.language) (param := param) hp hq

theorem formulaSyntax_all (param p : V) (hp : IsUFormula Presentation.language p) :
    formulaSyntax param (qqAll p)=guardedAllCode (formulaSyntax (binderParameters param) p) := by
  simpa [formulaConstruction,formulaSyntax] using
    formulaConstruction.result_all (L := Presentation.language) (param := param) hp rfl

theorem formulaSyntax_exs (param p : V) (hp : IsUFormula Presentation.language p) :
    formulaSyntax param (qqExs p)=guardedExsCode (formulaSyntax (binderParameters param) p) := by
  simpa [formulaConstruction,formulaSyntax] using
    formulaConstruction.result_exs (L := Presentation.language) (param := param) hp rfl

#print axioms formulaSyntax_defined
#print axioms formulaSyntax_graph
#print axioms formulaSyntax_total_unique
#print axioms formulaSyntax_invalid
#print axioms formulaSyntax_rel
#print axioms formulaSyntax_nrel
#print axioms formulaSyntax_verum
#print axioms formulaSyntax_falsum
#print axioms formulaSyntax_and
#print axioms formulaSyntax_or
#print axioms formulaSyntax_all
#print axioms formulaSyntax_exs
end M6.PA.NumericPAeqFormula

