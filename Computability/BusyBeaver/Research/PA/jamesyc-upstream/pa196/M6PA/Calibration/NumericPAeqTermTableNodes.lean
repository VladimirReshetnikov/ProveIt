module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermChildren
@[expose] public section

/-! Local cells of an arithmetic-term interpretation witness table. Children
are shared table records with exact shifted parameter packets. The source
term rank strictly decreases at each child. No table-existence theorem yet. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def node (param t out : V) : V := ⟪param,t,out⟫
@[simp] theorem node_param (param t out : V) : π₁ (node param t out)=param := by simp [node]
@[simp] theorem node_term (param t out : V) : π₁ (π₂ (node param t out))=t := by simp [node]
@[simp] theorem node_output (param t out : V) : π₂ (π₂ (node param t out))=out := by simp [node]

def Cell (C param t out : V) : Prop :=
  (∃ i, t=qqBvar i ∧ out=variableValue (nth param 2) (nth (nth param 0) i)) ∨
  (∃ i, t=qqFvar i ∧ out=variableValue (nth param 2) (nth (nth param 1) i)) ∨
  (t=qqFunc 0 0 0 ∧ out=zeroValue (nth param 2)) ∨
  (∃ u a, t=qqFunc 1 1 (u∷0) ∧ node (childParameters param) u a ∈ C ∧
    out=successorValue (nth param 2) a) ∨
  (∃ u v a b, t=qqFunc 2 2 (u∷(v∷0)) ∧
    node (binaryParameters param 1) u a ∈ C ∧ node (binaryParameters param 0) v b ∈ C ∧
    out=additionValue (nth param 2) a b) ∨
  (∃ u v a b, t=qqFunc 2 3 (u∷(v∷0)) ∧
    node (binaryParameters param 1) u a ∈ C ∧ node (binaryParameters param 0) v b ∈ C ∧
    out=multiplicationValue (nth param 2) a b)

attribute [local irreducible] variableValueGraph zeroValueGraph successorValueGraph
  binaryValueGraph childParametersGraph binaryParametersGraph
noncomputable def cellGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “C param t out. ∃ bs fs z, !nthDef bs param 0 ∧ !nthDef fs param 1 ∧ !nthDef z param 2 ∧
    ((∃ i x, !qqBvarDef t i ∧ !nthDef x bs i ∧ !variableValueGraph out z x) ∨
     (∃ i x, !qqFvarDef t i ∧ !nthDef x fs i ∧ !variableValueGraph out z x) ∨
     (!qqFuncDef t 0 0 0 ∧ !zeroValueGraph out z) ∨
     (∃ u a cp ts, !adjoinDef ts u 0 ∧ !qqFuncDef t 1 1 ts ∧
       !childParametersGraph cp param ∧ :⟪cp,u,a⟫:∈C ∧ !successorValueGraph out z a) ∨
     (∃ u v a b cp cq vs ts, !adjoinDef vs v 0 ∧ !adjoinDef ts u vs ∧ !qqFuncDef t 2 2 ts ∧
       !binaryParametersGraph cp param 1 ∧ !binaryParametersGraph cq param 0 ∧
       :⟪cp,u,a⟫:∈C ∧ :⟪cq,v,b⟫:∈C ∧ !additionValueGraph out z a b) ∨
     (∃ u v a b cp cq vs ts, !adjoinDef vs v 0 ∧ !adjoinDef ts u vs ∧ !qqFuncDef t 2 3 ts ∧
       !binaryParametersGraph cp param 1 ∧ !binaryParametersGraph cq param 0 ∧
       :⟪cp,u,a⟫:∈C ∧ :⟪cq,v,b⟫:∈C ∧ !multiplicationValueGraph out z a b))”

theorem cell_graph (C param t out : V) :
    cellGraph.val.Evalb ![C,param,t,out] ↔ Cell C param t out := by
  simp [cellGraph,Cell,node,variableValue_graph,zeroValue_graph,successorValue_graph,
    binaryValue_graph,childParameters_graph,binaryParameters_graph,additionValue,multiplicationValue,
    Matrix.comp_vecCons'']

theorem cell_monotone {C D param t out : V} (hCD : C⊆D) (h : Cell C param t out) :
    Cell D param t out := by
  rcases h with h|h|h|⟨u,a,ht,ha,hy⟩|⟨u,v,a,b,ht,ha,hb,hy⟩|⟨u,v,a,b,ht,ha,hb,hy⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u,a,ht,hCD ha,hy⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨u,v,a,b,ht,hCD ha,hCD hb,hy⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u,v,a,b,ht,hCD ha,hCD hb,hy⟩))))

theorem cell_bvar (C param i : V) :
    Cell C param (qqBvar i) (variableValue (nth param 2) (nth (nth param 0) i)) :=
  Or.inl ⟨i,rfl,rfl⟩
theorem cell_fvar (C param i : V) :
    Cell C param (qqFvar i) (variableValue (nth param 2) (nth (nth param 1) i)) :=
  Or.inr (Or.inl ⟨i,rfl,rfl⟩)
theorem cell_zero (C param : V) : Cell C param (qqFunc 0 0 0) (zeroValue (nth param 2)) :=
  Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))
theorem cell_successor {C param u a : V} (h : node (childParameters param) u a∈C) :
    Cell C param (qqFunc 1 1 (u∷0)) (successorValue (nth param 2) a) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨u,a,rfl,h,rfl⟩)))
theorem cell_addition {C param u v a b : V}
    (ha : node (binaryParameters param 1) u a∈C) (hb : node (binaryParameters param 0) v b∈C) :
    Cell C param (qqFunc 2 2 (u∷(v∷0))) (additionValue (nth param 2) a b) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨u,v,a,b,rfl,ha,hb,rfl⟩))))
theorem cell_multiplication {C param u v a b : V}
    (ha : node (binaryParameters param 1) u a∈C) (hb : node (binaryParameters param 0) v b∈C) :
    Cell C param (qqFunc 2 3 (u∷(v∷0))) (multiplicationValue (nth param 2) a b) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u,v,a,b,rfl,ha,hb,rfl⟩))))

#print axioms node_param
#print axioms node_term
#print axioms node_output
#print axioms cell_graph
#print axioms cell_monotone
#print axioms cell_bvar
#print axioms cell_fvar
#print axioms cell_zero
#print axioms cell_successor
#print axioms cell_addition
#print axioms cell_multiplication
end M6.PA.NumericPAeqTerm
