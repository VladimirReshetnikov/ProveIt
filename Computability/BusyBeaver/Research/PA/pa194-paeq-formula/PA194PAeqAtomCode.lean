import PA194PAeqAtoms
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def atomCode (_param _k r ts : V) : V :=
  if r=0 then equalityCode (termCode (nth ts 0)) (termCode (nth ts 1))
  else lessCode (termCode (nth ts 0)) (termCode (nth ts 1))
attribute [local irreducible] termCodeGraph equalityGraph lessGraph
noncomputable def atomGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out param k r ts. ∃ s t ss tt,
    !nthDef s ts 0 ∧ !nthDef t ts 1 ∧ !termCodeGraph ss s ∧ !termCodeGraph tt t ∧
    ((r=0 ∧ !equalityGraph out ss tt) ∨ (r≠0 ∧ !lessGraph out ss tt))”
theorem atom_graph (out param k r ts : V) : atomGraph.val.Evalb ![out,param,k,r,ts] ↔
    out=atomCode param k r ts := by
  by_cases hr : r=0 <;> simp [atomGraph,atomCode,hr,Matrix.comp_vecCons'']
instance atom_defined : 𝚺₁-Function₄ (atomCode : V→V→V→V→V) via atomGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! atom_graph (v 0) (v 1) (v 2) (v 3) (v 4)


#print axioms atom_graph
#print axioms atom_defined
end PA194PAeqTermBlueprint
