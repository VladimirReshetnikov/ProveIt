module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeParameters
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! Total model functions with explicit default behavior, agreeing with guarded
atom translation on covered inputs. No computational extraction from Prop. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Decode the HFS variable tag after truncated predecessor. Unknown tags return
zero; out-of-range indices retain Foundation nth's zero default. -/
noncomputable def totalLabel (t b f : V) : V := by
  classical
  exact if π₁ (t-1)=0 then nth b (π₂ (t-1)) else
    if π₁ (t-1)=1 then nth f (π₂ (t-1)) else 0

noncomputable def totalLabelGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y t b f. ∃ d tag i, !subDef d t 1 ∧ !pi₁Def tag d ∧ !pi₂Def i d ∧
    ((tag=0 ∧ !nthDef y b i) ∨ (tag=1 ∧ !nthDef y f i) ∨
     (tag≠0 ∧ tag≠1 ∧ y=0))”

theorem totalLabel_graph (y t b f : V) :
    totalLabelGraph.val.Evalb ![y,t,b,f] ↔ y=totalLabel t b f := by
  classical
  by_cases h0 : π₁ (t-1)=0
  · simp [totalLabelGraph,totalLabel,h0]
  · by_cases h1 : π₁ (t-1)=1 <;> simp [totalLabelGraph,totalLabel,h0,h1]

attribute [local irreducible] totalLabelGraph

instance totalLabel_defined : 𝚺ᴬ₁-Function₃ (totalLabel : V → V → V → V) via totalLabelGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3]=v := by
      ext i; fin_cases i <;> rfl
    simpa only [hv] using! totalLabel_graph (v 0) (v 1) (v 2) (v 3)

@[simp] theorem totalLabel_bvar (i b f : V) : totalLabel (qqBvar i) b f=nth b i := by
  simp [totalLabel,qqBvar]
@[simp] theorem totalLabel_fvar (i b f : V) : totalLabel (qqFvar i) b f=nth f i := by
  simp [totalLabel,qqFvar]

theorem totalLabel_agrees {y t b f : V} (h : VariableLabel y t b f) :
    y=totalLabel t b f := by
  rcases h with ⟨i,_,rfl,rfl⟩ | ⟨i,_,rfl,rfl⟩ <;> simp

/-- Unknown source relation tags return zero. This is not a native truth test. -/
noncomputable def totalHead (r a d z : V) : V := by
  classical
  exact if r=0 then eval neighborhoodExpr a d z 0 else
    if r=1 then eval membershipExpr a d z 0 else 0

noncomputable def totalHeadGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y r a d z. (r=0 ∧ !(graph neighborhoodExpr) y a d z 0) ∨
    (r=1 ∧ !(graph membershipExpr) y a d z 0) ∨ (r≠0 ∧ r≠1 ∧ y=0)”

attribute [local irreducible] ActualArithmeticGraph.graph neighborhoodExpr membershipExpr

theorem totalHead_graph (y r a d z : V) :
    totalHeadGraph.val.Evalb ![y,r,a,d,z] ↔ y=totalHead r a d z := by
  classical
  by_cases h0 : r=0
  · simp [totalHeadGraph,totalHead,h0,graph_correct,Matrix.comp_vecCons'']
  · by_cases h1 : r=1 <;>
      simp [totalHeadGraph,totalHead,h0,h1,graph_correct,Matrix.comp_vecCons'']

attribute [local irreducible] totalHeadGraph

instance totalHead_defined : 𝚺ᴬ₁-Function₄ (totalHead : V → V → V → V → V) via totalHeadGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by
      ext i; fin_cases i <;> rfl
    simpa only [hv] using! totalHead_graph (v 0) (v 1) (v 2) (v 3) (v 4)

theorem totalHead_agrees {y r a d z : V} (h : AtomHead y r a d z) :
    y=totalHead r a d z := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [totalHead]

/-- Arity and vector length are checked by the guarded relation, not this total
extension. Missing parameter or term-vector entries use nth defaults. -/
noncomputable def totalAtom (param _k r ts : V) : V :=
  totalHead r (totalLabel (nth ts 0) (nth param 0) (nth param 1))
    (totalLabel (nth ts 1) (nth param 0) (nth param 1)) (nth param 3)

noncomputable def totalAtomGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y param k r ts. ∃ b f z t s a d,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 3 ∧
    !nthDef t ts 0 ∧ !nthDef s ts 1 ∧ !totalLabelGraph a t b f ∧
    !totalLabelGraph d s b f ∧ !totalHeadGraph y r a d z”

theorem totalAtom_graph (y param k r ts : V) :
    totalAtomGraph.val.Evalb ![y,param,k,r,ts] ↔ y=totalAtom param k r ts := by
  simp [totalAtomGraph,totalAtom,totalLabel_graph,totalHead_graph,Matrix.comp_vecCons'']

attribute [local irreducible] totalAtomGraph

instance totalAtom_defined : 𝚺ᴬ₁-Function₄ (totalAtom : V → V → V → V → V) via totalAtomGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by
      ext i; fin_cases i <;> rfl
    simpa only [hv] using! totalAtom_graph (v 0) (v 1) (v 2) (v 3) (v 4)

theorem totalAtom_total_unique (param k r ts : V) :
    ∃! y, totalAtomGraph.val.Evalb ![y,param,k,r,ts] := by
  refine ⟨totalAtom param k r ts,(totalAtom_graph _ _ _ _ _).mpr rfl,?_⟩
  intro y hy
  exact (totalAtom_graph _ _ _ _ _).mp hy

theorem totalAtom_agrees {y k r ts b f lo z : V}
    (h : AtomTranslation y k r ts b f lo z) :
    y=totalAtom (parameters b f lo z) k r ts := by
  rcases h with ⟨_,_,_,a,d,ha,hd,hh⟩
  have ea := totalLabel_agrees ha
  have ed := totalLabel_agrees hd
  simpa [totalAtom,← ea,← ed] using totalHead_agrees hh

#print axioms totalLabel_graph
#print axioms totalLabel_defined
#print axioms totalLabel_bvar
#print axioms totalLabel_fvar
#print axioms totalLabel_agrees
#print axioms totalHead_graph
#print axioms totalHead_defined
#print axioms totalHead_agrees
#print axioms totalAtom_graph
#print axioms totalAtom_defined
#print axioms totalAtom_total_unique
#print axioms totalAtom_agrees
end M6.PA.RelationalSource.Numeric

