module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import PA196.Arithmetic.CompilerInvariantFormula
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CompilerSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CommandStep M6.PA.SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_table_realizes (n words : V) : TableRealizes (repeatVec 0 n) words := by
  intro i a h
  have hz : nth (repeatVec (0:V) n) i=0 := by
    by_cases hi : i<n
    · exact nth_repeatVec 0 n hi
    · apply nth_lt_len
      simpa using le_of_not_gt hi
  rw [hz] at h
  exact False.elim ((ne_of_lt (lt_add_one a)).elim (by simpa using h.symm))

theorem rows_preserve (n previous words : V) (ih : TableRealizes previous words) :
    TableRealizes (CheckerRows.rows n previous) (CompilerRows.rows n words) := by
  intro i a h
  by_cases hi : i<n
  · rw [CheckerRows.rows_nth _ _ _ hi] at h
    rw [CompilerRows.rows_nth _ _ _ hi]
    exact rule_sound previous words (decodeLeft i) (decodeRight i) a ih h
  · have hz : nth (CheckerRows.rows n previous) i=0 :=
      nth_lt_len (by simpa [CheckerRows.rows_length] using le_of_not_gt hi)
    rw [hz] at h
    exact False.elim ((ne_of_lt (lt_add_one a)).elim (by simpa using h.symm))

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]
/-- Full PA induction on the explicitly presented quantified invariant.
The induction variable ranges over every element of the arithmetic model. -/
theorem fuel_invariant (fuel bound : V) :
    TableRealizes (Checker.tableValue fuel bound)
      (Compiler.tableValue fuel bound) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ fuel : V, ∀ bound : V,
      TableRealizes (Checker.tableValue fuel bound)
        (Compiler.tableValue fuel bound) := by
    refine InductionScheme.succ_induction (C := Set.univ)
      (P := fun fuel : V => ∀ bound : V,
        TableRealizes (Checker.tableValue fuel bound)
          (Compiler.tableValue fuel bound)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb fuelInvariantFormula,by trivial,?_⟩
      intro n
      simpa using (fuelInvariant_formula (V:=V) n).symm
    · intro b
      rw [Checker.table_zero]
      exact zero_table_realizes _ _
    · intro n ih b
      rw [Checker.table_succ,Compiler.table_succ]
      exact rows_preserve _ _ _ (ih b)
  exact all fuel bound

theorem accepted_compiler_realizes (code out : V)
    (h : Checker.verifyValue code=out+1) :
    Realizes (Compiler.compiledValue code) out := by
  exact fuel_invariant (decodeLeft code) (decodeRight code) (decodeRight code) out h
end Peano
#print axioms rows_preserve
#print axioms fuel_invariant
#print axioms accepted_compiler_realizes
end PA196.Arithmetic.CompilerSoundness

