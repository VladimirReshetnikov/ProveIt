module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCheckerRows
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCheckerBlueprint
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal ActualCheckerRows
attribute [local irreducible] ActualCheckerRows.rowsGraph repeatVecDef

/-- The outer fuel recursion stores a finite HFS table of bound+1 entries.
Fuel zero is all rejection; every successor computes a row using only the
preceding table, so no function-valued recursive state is assumed. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := repeatVecDef.rew (Rew.subst ![#0,‘0’,‘#1+1’])
  succ := rowsGraph.rew (Rew.subst ![#0,‘#3+1’,#1])

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def construction : PR.Construction V blueprint where
  zero := fun p => repeatVec 0 (p 0+1)
  succ := fun p _ previous => rows (p 0+1) previous
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by simp [blueprint,rows_graph]

noncomputable def tableValue (fuel bound : V) : V := construction.result ![bound] fuel
noncomputable def tableGraph : 𝚺ᴬ₁.Semisentence 3 := blueprint.resultDef
@[simp] theorem table_zero (bound : V) : tableValue 0 bound=repeatVec 0 (bound+1) := by
  simp [tableValue,construction]
@[simp] theorem table_succ (fuel bound : V) : tableValue (fuel+1) bound=rows (bound+1) (tableValue fuel bound) := by
  simp [tableValue,construction]

theorem table_graph (z fuel bound : V) :
    tableGraph.val.Evalb ![z,fuel,bound] ↔ z=tableValue fuel bound := by
  simpa [tableGraph,tableValue,Matrix.constant_eq_singleton] using (construction (V := V)).result_defined_iff ![z,fuel,bound]

attribute [local irreducible] tableGraph

/-- Result zero rejects; result a+1 is a successful proof of formula a. -/
noncomputable def verifyValue (code : V) : V :=
  nth (tableValue (decodeLeft code) (decodeRight code)) (decodeRight code)
noncomputable def verifyGraph : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “z code. ∃ fuel tree table,
    !decodeGraph fuel tree code ∧ !tableGraph table fuel tree ∧ !nthDef z table tree”

theorem verify_graph (z code : V) : verifyGraph.val.Evalb ![z,code] ↔ z=verifyValue code := by
  simp [verifyGraph,decode_graph,table_graph,verifyValue]
theorem verify_total_unique (code : V) : ∃! z,verifyGraph.val.Evalb ![z,code] := by
  exact ⟨verifyValue code,(verify_graph _ _).mpr rfl,fun z hz => (verify_graph _ _).mp hz⟩

noncomputable def totalSentence : ArithmeticSentence := “∀ code, ∃ z, !verifyGraph z code”
theorem pa_proves_verify_total : theory ⊢ totalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [totalSentence,models_iff,verify_graph]

#print axioms table_graph
#print axioms verify_graph
#print axioms pa_proves_verify_total
end M6.PA.ActualCheckerBlueprint

