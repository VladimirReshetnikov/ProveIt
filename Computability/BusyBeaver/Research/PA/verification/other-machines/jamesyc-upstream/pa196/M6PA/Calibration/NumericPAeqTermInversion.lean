module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTables
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cell_bvar_iff (C param i out : V) : Cell C param (qqBvar i) out ↔
    out=variableValue (nth param 2) (nth (nth param 0) i) := by
  simp [Cell,qqBvar,qqFvar,qqFunc]
theorem cell_fvar_iff (C param i out : V) : Cell C param (qqFvar i) out ↔
    out=variableValue (nth param 2) (nth (nth param 1) i) := by
  simp [Cell,qqBvar,qqFvar,qqFunc]
theorem cell_zero_iff (C param out : V) : Cell C param (qqFunc 0 0 0) out ↔
    out=zeroValue (nth param 2) := by
  simp [Cell,qqBvar,qqFvar,qqFunc]
theorem cell_successor_iff (C param u out : V) : Cell C param (qqFunc 1 1 (u∷0)) out ↔
    ∃ a, node (childParameters param) u a∈C ∧ out=successorValue (nth param 2) a := by
  simp [Cell,qqBvar,qqFvar,qqFunc]
theorem cell_addition_iff (C param u v out : V) : Cell C param (qqFunc 2 2 (u∷(v∷0))) out ↔
    ∃ a b, node (binaryParameters param 1) u a∈C ∧ node (binaryParameters param 0) v b∈C ∧
      out=additionValue (nth param 2) a b := by
  simp [Cell,qqBvar,qqFvar,qqFunc]
theorem cell_multiplication_iff (C param u v out : V) : Cell C param (qqFunc 2 3 (u∷(v∷0))) out ↔
    ∃ a b, node (binaryParameters param 1) u a∈C ∧ node (binaryParameters param 0) v b∈C ∧
      out=multiplicationValue (nth param 2) a b := by
  simp [Cell,qqBvar,qqFvar,qqFunc]

theorem table_root_cell {C param t out : V} (hc : ValidTable C) (hm : node param t out∈C) :
    Cell C param t out := by simpa using hc (node param t out) hm

theorem witness_bvar_iff (param i out : V) : ValueWitness param (qqBvar i) out ↔
    out=variableValue (nth param 2) (nth (nth param 0) i) := by
  constructor
  · rintro ⟨C,hc,hm⟩; exact (cell_bvar_iff _ _ _ _).mp (table_root_cell hc hm)
  · rintro rfl; exact witness_bvar _ _
theorem witness_fvar_iff (param i out : V) : ValueWitness param (qqFvar i) out ↔
    out=variableValue (nth param 2) (nth (nth param 1) i) := by
  constructor
  · rintro ⟨C,hc,hm⟩; exact (cell_fvar_iff _ _ _ _).mp (table_root_cell hc hm)
  · rintro rfl; exact witness_fvar _ _
theorem witness_zero_iff (param out : V) : ValueWitness param (qqFunc 0 0 0) out ↔
    out=zeroValue (nth param 2) := by
  constructor
  · rintro ⟨C,hc,hm⟩; exact (cell_zero_iff _ _ _).mp (table_root_cell hc hm)
  · rintro rfl; exact witness_zero _
theorem witness_successor_iff (param u out : V) : ValueWitness param (qqFunc 1 1 (u∷0)) out ↔
    ∃ a, ValueWitness (childParameters param) u a ∧ out=successorValue (nth param 2) a := by
  constructor
  · rintro ⟨C,hc,hm⟩
    obtain ⟨a,ha,hy⟩ := (cell_successor_iff _ _ _ _).mp (table_root_cell hc hm)
    exact ⟨a,⟨C,hc,ha⟩,hy⟩
  · rintro ⟨a,ha,rfl⟩; exact witness_successor ha
theorem witness_addition_iff (param u v out : V) : ValueWitness param (qqFunc 2 2 (u∷(v∷0))) out ↔
    ∃ a b, ValueWitness (binaryParameters param 1) u a ∧ ValueWitness (binaryParameters param 0) v b ∧
      out=additionValue (nth param 2) a b := by
  constructor
  · rintro ⟨C,hc,hm⟩
    obtain ⟨a,b,ha,hb,hy⟩ := (cell_addition_iff _ _ _ _ _).mp (table_root_cell hc hm)
    exact ⟨a,b,⟨C,hc,ha⟩,⟨C,hc,hb⟩,hy⟩
  · rintro ⟨a,b,ha,hb,rfl⟩; exact witness_addition ha hb
theorem witness_multiplication_iff (param u v out : V) : ValueWitness param (qqFunc 2 3 (u∷(v∷0))) out ↔
    ∃ a b, ValueWitness (binaryParameters param 1) u a ∧ ValueWitness (binaryParameters param 0) v b ∧
      out=multiplicationValue (nth param 2) a b := by
  constructor
  · rintro ⟨C,hc,hm⟩
    obtain ⟨a,b,ha,hb,hy⟩ := (cell_multiplication_iff _ _ _ _ _).mp (table_root_cell hc hm)
    exact ⟨a,b,⟨C,hc,ha⟩,⟨C,hc,hb⟩,hy⟩
  · rintro ⟨a,b,ha,hb,rfl⟩; exact witness_multiplication ha hb

#print axioms cell_bvar_iff
#print axioms cell_fvar_iff
#print axioms cell_zero_iff
#print axioms cell_successor_iff
#print axioms cell_addition_iff
#print axioms cell_multiplication_iff
#print axioms table_root_cell
#print axioms witness_bvar_iff
#print axioms witness_fvar_iff
#print axioms witness_zero_iff
#print axioms witness_successor_iff
#print axioms witness_addition_iff
#print axioms witness_multiplication_iff
end M6.PA.NumericPAeqTerm

