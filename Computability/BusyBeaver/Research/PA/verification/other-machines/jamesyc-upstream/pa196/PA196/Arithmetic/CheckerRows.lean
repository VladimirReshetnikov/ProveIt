module
public import PA196.Arithmetic.CheckerRule
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CheckerRows
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA.SourceCantorInternal CheckerRule Scalar

/-- Append exactly one evaluated V1 tree to the HFS row vector at each step.
The parameter is the preceding fuel-round table, not a recursive function. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “z previous. z=0”
  succ := .mkSigma “u z i previous. ∃ tag payload value,
    !decodeGraph tag payload i ∧ !ruleGraph value previous tag payload ∧ !concatDef u z value”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ => 0
  succ := fun p i z => concat z (ruleValue (p 0) (decodeLeft i) (decodeRight i))
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by
    simp [blueprint,decode_graph,ruleGraph,graph_correct,ruleValue]

noncomputable def rows (n previous : V) : V := construction.result ![previous] n
noncomputable def rowsGraph : 𝚺ᴬ₁.Semisentence 3 := blueprint.resultDef

@[simp] theorem rows_zero (previous : V) : rows 0 previous=0 := by
  simp [rows,construction]
@[simp] theorem rows_succ (n previous : V) :
    rows (n+1) previous = concat (rows n previous)
      (ruleValue previous (decodeLeft n) (decodeRight n)) := by
  simp [rows,construction]

theorem rows_graph (z n previous : V) :
    rowsGraph.val.Evalb ![z,n,previous] ↔ z=rows n previous := by
  simpa [rowsGraph,rows,Matrix.constant_eq_singleton] using (construction (V := V)).result_defined_iff ![z,n,previous]

instance rows_defined : 𝚺ᴬ₁-Function₂ (rows : V → V → V) via rowsGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl|rfl|rfl <;> rfl
  rw [hv]
  exact rows_graph _ _ _
instance rows_definable : 𝚺ᴬ₁-Function₂ (rows : V → V → V) := rows_defined.to_definable

theorem rows_length (n previous : V) : len (rows n previous)=n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [ih]

theorem rows_nth (n previous i : V) (hi : i<n) :
    nth (rows n previous) i = ruleValue previous (decodeLeft i) (decodeRight i) := by
  induction n using ISigma1.sigma1_succ_induction generalizing i
  · definability
  case zero => simp at hi
  case succ n ih =>
    rw [rows_succ]
    by_cases he : i=n
    · subst i
      exact concat_nth_len' _ _ (rows_length _ _)
    · have hlt : i<n := lt_of_le_of_ne ((le_iff_lt_succ).mpr hi) he
      rw [concat_nth_lt _ _ (by simpa [rows_length] using hlt)]
      exact ih i hlt

#print axioms rows_graph
#print axioms rows_length
#print axioms rows_nth
end PA196.Arithmetic.CheckerRows

