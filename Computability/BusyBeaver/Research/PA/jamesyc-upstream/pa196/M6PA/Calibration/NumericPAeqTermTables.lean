module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTableNodes
@[expose] public section

/-! Finite HFS witness tables with genuine bounded Sigma-one checks. Local
support is monotone, so existing tables can be joined and a new root inserted.
These constructor witnesses do not yet supply arbitrary source-term totality. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ValidTable (C : V) : Prop := ∀ r∈C, Cell C (π₁ r) (π₁ (π₂ r)) (π₂ (π₂ r))
attribute [local irreducible] cellGraph
noncomputable def validTableGraph : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “C. ∀ r<C, r∈C → ∃ param ty t out,
    !pi₁Def param r ∧ !pi₂Def ty r ∧ !pi₁Def t ty ∧ !pi₂Def out ty ∧ !cellGraph C param t out”
theorem validTable_graph (C : V) : validTableGraph.val.Evalb ![C] ↔ ValidTable C := by
  simp only [validTableGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [cell_graph,ValidTable,Matrix.comp_vecCons'']
  exact ⟨fun h r hr => h r (lt_of_mem hr) hr, fun h r _ hr => h r hr⟩

def ValueWitness (param t out : V) : Prop := ∃ C : V, ValidTable C ∧ node param t out∈C
noncomputable def valueWitnessGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param t. ∃ C, !validTableGraph C ∧ :⟪param,t,out⟫:∈C”
theorem valueWitness_graph (out param t : V) :
    valueWitnessGraph.val.Evalb ![out,param,t] ↔ ValueWitness param t out := by
  simp [valueWitnessGraph,validTable_graph,ValueWitness,node,Matrix.comp_vecCons'']

theorem validTable_empty : ValidTable (0:V) := by intro r hr; simpa using hr

theorem validTable_union {C D : V} (hc : ValidTable C) (hd : ValidTable D) : ValidTable (C∪D) := by
  intro r hr
  rcases mem_cup_iff.mp hr with h|h
  · exact cell_monotone (by simp) (hc r h)
  · exact cell_monotone (by simp) (hd r h)

theorem validTable_insert {C param t out : V} (hc : ValidTable C) (hroot : Cell C param t out) :
    ValidTable (insert (node param t out) C) := by
  intro r hr
  rcases mem_bitInsert_iff.mp hr with rfl|hr
  · simp only [node_param,node_term,node_output]
    exact cell_monotone (by simp) hroot
  · exact cell_monotone (by simp) (hc r hr)

theorem witness_of_cell {C param t out : V} (hc : ValidTable C) (hroot : Cell C param t out) :
    ValueWitness param t out :=
  ⟨insert (node param t out) C,validTable_insert hc hroot,by simp⟩

theorem witness_bvar (param i : V) :
    ValueWitness param (qqBvar i) (variableValue (nth param 2) (nth (nth param 0) i)) :=
  witness_of_cell validTable_empty (cell_bvar 0 param i)
theorem witness_fvar (param i : V) :
    ValueWitness param (qqFvar i) (variableValue (nth param 2) (nth (nth param 1) i)) :=
  witness_of_cell validTable_empty (cell_fvar 0 param i)
theorem witness_zero (param : V) : ValueWitness param (qqFunc 0 0 0) (zeroValue (nth param 2)) :=
  witness_of_cell validTable_empty (cell_zero 0 param)
theorem witness_successor {param u a : V} (h : ValueWitness (childParameters param) u a) :
    ValueWitness param (qqFunc 1 1 (u∷0)) (successorValue (nth param 2) a) := by
  obtain ⟨C,hc,ha⟩ := h
  exact witness_of_cell hc (cell_successor ha)
theorem witness_addition {param u v a b : V}
    (ha : ValueWitness (binaryParameters param 1) u a) (hb : ValueWitness (binaryParameters param 0) v b) :
    ValueWitness param (qqFunc 2 2 (u∷(v∷0))) (additionValue (nth param 2) a b) := by
  obtain ⟨C,hc,ha⟩ := ha
  obtain ⟨D,hd,hb⟩ := hb
  exact witness_of_cell (validTable_union hc hd) (cell_addition (by simp [ha]) (by simp [hb]))
theorem witness_multiplication {param u v a b : V}
    (ha : ValueWitness (binaryParameters param 1) u a) (hb : ValueWitness (binaryParameters param 0) v b) :
    ValueWitness param (qqFunc 2 3 (u∷(v∷0))) (multiplicationValue (nth param 2) a b) := by
  obtain ⟨C,hc,ha⟩ := ha
  obtain ⟨D,hd,hb⟩ := hb
  exact witness_of_cell (validTable_union hc hd) (cell_multiplication (by simp [ha]) (by simp [hb]))

#print axioms validTable_graph
#print axioms valueWitness_graph
#print axioms validTable_empty
#print axioms validTable_union
#print axioms validTable_insert
#print axioms witness_of_cell
#print axioms witness_bvar
#print axioms witness_fvar
#print axioms witness_zero
#print axioms witness_successor
#print axioms witness_addition
#print axioms witness_multiplication
end M6.PA.NumericPAeqTerm
