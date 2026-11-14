import PA194PAeqFormulaConstruction
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] 

noncomputable def formulaCode (param p : V) : V :=
  formulaConstruction.result ℒₒᵣ param p
noncomputable def formulaCodeGraph : 𝚺₁.Semisentence 3 :=
  formulaBlueprint.result ℒₒᵣ
instance formulaCode_defined :
    𝚺₁-Function₂ (formulaCode : V → V → V) via formulaCodeGraph :=
  formulaConstruction.result_defined (L := ℒₒᵣ)

theorem formulaCode_graph (out param p : V) :
    formulaCodeGraph.val.Evalb ![out,param,p] ↔ out=formulaCode param p :=
  formulaCode_defined.defined ![out,param,p]
theorem formulaCode_total_unique (param p : V) :
    ∃! out,formulaCodeGraph.val.Evalb ![out,param,p] :=
  ⟨formulaCode param p,(formulaCode_graph _ _ _).mpr rfl,
    fun _ h => (formulaCode_graph _ _ _).mp h⟩
theorem formulaCode_invalid (param p : V) (h : ¬IsUFormula ℒₒᵣ p) :
    formulaCode param p=0 :=
  formulaConstruction.result_prop_not (L := ℒₒᵣ) param h

theorem formulaCode_rel (param k r ts : V) (hr : (ℒₒᵣ).IsRel k r)
    (ht : IsUTermVec ℒₒᵣ k ts) :
    formulaCode param (qqRel k r ts)=atomCode param k r ts :=
  formulaConstruction.result_rel (L := ℒₒᵣ) (param := param) hr ht

theorem formulaCode_nrel (param k r ts : V) (hr : (ℒₒᵣ).IsRel k r)
    (ht : IsUTermVec ℒₒᵣ k ts) :
    formulaCode param (qqNRel k r ts)=neg PA194PAeq.language (atomCode param k r ts) :=
  formulaConstruction.result_nrel (L := ℒₒᵣ) (param := param) hr ht

theorem formulaCode_verum (param : V) : formulaCode param qqVerum=qqVerum :=
  formulaConstruction.result_verum (L := ℒₒᵣ) (param := param)
theorem formulaCode_falsum (param : V) : formulaCode param qqFalsum=qqFalsum :=
  formulaConstruction.result_falsum (L := ℒₒᵣ) (param := param)

theorem formulaCode_and (param p q : V)
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    formulaCode param (qqAnd p q)=qqAnd (formulaCode param p) (formulaCode param q) :=
  formulaConstruction.result_and (L := ℒₒᵣ) (param := param) hp hq

theorem formulaCode_or (param p q : V)
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    formulaCode param (qqOr p q)=qqOr (formulaCode param p) (formulaCode param q) :=
  formulaConstruction.result_or (L := ℒₒᵣ) (param := param) hp hq

theorem formulaCode_all (param p : V) (hp : IsUFormula ℒₒᵣ p) :
    formulaCode param (qqAll p)=qqAll (formulaCode param p) := by
  simpa [formulaConstruction,formulaCode] using
    formulaConstruction.result_all (L := ℒₒᵣ) (param := param) hp

theorem formulaCode_exs (param p : V) (hp : IsUFormula ℒₒᵣ p) :
    formulaCode param (qqExs p)=qqExs (formulaCode param p) := by
  simpa [formulaConstruction,formulaCode] using
    formulaConstruction.result_exs (L := ℒₒᵣ) (param := param) hp

#print axioms formulaCode_defined
#print axioms formulaCode_graph
#print axioms formulaCode_total_unique
#print axioms formulaCode_invalid
#print axioms formulaCode_rel
#print axioms formulaCode_nrel
#print axioms formulaCode_verum
#print axioms formulaCode_falsum
#print axioms formulaCode_and
#print axioms formulaCode_or
#print axioms formulaCode_all
#print axioms formulaCode_exs
end PA194PAeqTermBlueprint

