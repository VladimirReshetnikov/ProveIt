import PA194BudgetSkeleton
import DiophantineConsistency.PRAFiniteFunctionCodes
namespace PA194SourcePRACodes
open LO LO.FirstOrder M6.PA.RelationalSource
open DiophantineConsistency.PRAFiniteFunctionCodes
open PA194FormulaShiftPR PA194DepthPR PA194BudgetSkeleton

theorem unaryCode_of_primrec (f : Nat → Nat) (hf : Primrec f) :
    ∃ c : Code 1, ∀ n : Nat, eval c (List.Vector.ofFn (fun _ : Fin 1 => n)) = f n := by
  have hp : Primrec (fun v : List.Vector Nat 1 => f (v.get 0)) :=
    hf.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
  obtain ⟨c, hc⟩ := exists_code_of_primrec hp
  refine ⟨c, fun n => ?_⟩
  have h := congrFun hc (List.Vector.ofFn (fun _ : Fin 1 => n))
  simpa using h

theorem shift_has_PRA_code : ∃ c : Code 1, ∀ (n : Nat),
    eval c (List.Vector.ofFn (fun _ : Fin 1 => n)) = formulaShiftCode n :=
  unaryCode_of_primrec _ formulaShiftCode_primrec

theorem budget_has_PRA_code : ∃ c : Code 1, ∀ (n : Nat),
    eval c (List.Vector.ofFn (fun _ : Fin 1 => n)) = budgetCode n :=
  unaryCode_of_primrec _ budgetCode_primrec

theorem depth_has_PRA_code : ∃ c : Code 1, ∀ (n : Nat),
    eval c (List.Vector.ofFn (fun _ : Fin 1 => n)) = depthCode n :=
  unaryCode_of_primrec _ depthCode_primrec

theorem shift_code_correct : ∃ c : Code 1, ∀ {n : Nat} (p : Semiproposition language n),
    eval c (List.Vector.ofFn (fun _ : Fin 1 => Encodable.encode p)) =
      Encodable.encode (Semiformula.shift p) := by
  obtain ⟨c, hc⟩ := shift_has_PRA_code
  exact ⟨c, fun p => (hc _).trans (formulaShiftCode_correct p)⟩

theorem depth_code_correct : ∃ c : Code 1, ∀ {n : Nat} (p : Semiproposition language n),
    eval c (List.Vector.ofFn (fun _ : Fin 1 => Encodable.encode p)) = depth p := by
  obtain ⟨c, hc⟩ := depth_has_PRA_code
  exact ⟨c, fun p => (hc _).trans (depthCode_correct p)⟩

theorem budget_code_correct : ∃ c : Code 1, ∀ {Γ : List (Proposition language)}
    (d : LO.FirstOrder.Derivation Γ),
    eval c (List.Vector.ofFn (fun _ : Fin 1 => treeCode (treeOf d))) =
      PA194Logic.Relational.Source.listFoundationBudget d := by
  obtain ⟨c, hc⟩ := budget_has_PRA_code
  exact ⟨c, fun d => (hc _).trans (coded_treeOf_correct d)⟩

#print axioms shift_code_correct
#print axioms depth_code_correct
#print axioms budget_code_correct
#print axioms unaryCode_of_primrec
#print axioms shift_has_PRA_code
#print axioms budget_has_PRA_code
#print axioms depth_has_PRA_code
end PA194SourcePRACodes
