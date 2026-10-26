import DiophantineConsistency.FoundationHAInduction

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAInductionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAInduction FoundationHAClosure
open SetTheory.PA HA

/-- Bound index two is the original induction variable below these two binders.
Free parameters zero and seven must not be captured. -/
def nestedSource : Semiformula ℒₒᵣ Nat 1 :=
  “∀ y, ∃ z, #2 + y = z + &7 ∨ &0 < #2”

def sparseSource : Semiformula ℒₒᵣ Nat 1 := “#0 + &0 = &7”

def nestedTarget : Formula := .all (.ex
  (.and (.eq (.add (.var 2) (.var 1)) (.var 9)) (.eq (.var 0) (.var 2))))

theorem literal_zero_slots : Formula.subst Formula.substZero nestedTarget =
    .all (.ex (.and (.eq (.add .zero (.var 1)) (.var 8)) (.eq (.var 0) .zero))) := rfl

theorem literal_succ_slots : Formula.subst Formula.substSuccVar nestedTarget =
    .all (.ex (.and (.eq (.add (.succ (.var 2)) (.var 1)) (.var 9))
      (.eq (.var 0) (.succ (.var 2))))) := rfl

theorem literal_add_one_slots : Formula.subst addOneSubst nestedTarget =
    .all (.ex (.and (.eq (.add (.add (.var 2) (.succ .zero)) (.var 1)) (.var 9))
      (.eq (.var 0) (.add (.var 2) (.succ .zero))))) := rfl

/-- Both inner binders stay fixed, the induction slot stays at two, and the
free parameter moves from nine to ten for the temporary equality hole. -/
theorem literal_hole_slots : Formula.rename (SetTheory.up Nat.succ) nestedTarget =
    .all (.ex (.and (.eq (.add (.var 2) (.var 1)) (.var 10))
      (.eq (.var 0) (.var 2)))) := rfl

theorem zero_really_removes_parameter_slot :
    Formula.subst Formula.substZero (.eq (.var 0) (.var 8)) ≠
      .eq .zero (.var 8) := by
  intro h
  cases h

theorem succ_really_preserves_parameter_slot :
    Formula.subst Formula.substSuccVar (.eq (.var 0) (.var 8)) ≠
      .eq (.succ (.var 0)) (.var 7) := by
  intro h
  cases h

/-- This is an actual HA derivation under its still-open formula assumption. -/
theorem nested_open_replacement : Relative Formula.Ax_s
    [Formula.subst addOneSubst nestedTarget]
    (Formula.subst Formula.substSuccVar nestedTarget) :=
  add_one_replacement nestedTarget (Relative.hypothesis List.mem_cons_self)

theorem nested_replacement_imp : Proves (.imp
    (Formula.subst addOneSubst nestedTarget)
    (Formula.subst Formula.substSuccVar nestedTarget)) :=
  Relative.imp_intro nested_open_replacement

theorem source_zero_binding :
    formula (nestedSource ⇜ (fun _ => (‘0’ : SyntacticTerm ℒₒᵣ)))ᴺ =
      Formula.subst Formula.substZero (formula nestedSourceᴺ) :=
  translated_zero nestedSource

theorem source_step_binding :
    formula (nestedSource ⇜ (fun _ => (‘#0 + 1’ : SyntacticSemiterm ℒₒᵣ 1)))ᴺ =
      Formula.subst addOneSubst (formula nestedSourceᴺ) :=
  translated_add_one nestedSource

theorem substitution_with_free_parameter :
    formula (nestedSourceᴺ ⇜ (fun _ => (‘#0 + &7’ : SyntacticSemiterm ℒₒᵣ 1))) =
      Formula.subst (replaceZero (.add (.var 0) (.var 8))) (formula nestedSourceᴺ) :=
  formula_subst_same _ _

theorem actual_curried_source (φ : Semiformula ℒₒᵣ Nat 1) :
    LO.FirstOrder.Arithmetic.succInd φ =
      ((φ ⇜ (fun _ => (‘0’ : SyntacticTerm ℒₒᵣ))) 🡒
        ((∀⁰ (φ 🡒 (φ ⇜ (fun _ => (‘#0 + 1’ : SyntacticSemiterm ℒₒᵣ 1))))) 🡒 ∀⁰ φ)) :=
  source_succInd φ

theorem actual_nested_open :
    Proves (formula (LO.FirstOrder.Arithmetic.succInd nestedSource)ᴺ) :=
  succInd_open nestedSource

theorem actual_nested_closed :
    Proves (sentence (Semiformula.univCl
      (LO.FirstOrder.Arithmetic.succInd nestedSource))ᴺ) := succInd_closed nestedSource

theorem actual_sparse_closed :
    Proves (sentence (Semiformula.univCl
      (LO.FirstOrder.Arithmetic.succInd sparseSource))ᴺ) :=
  induction_axiom ⟨sparseSource, Set.mem_univ _, rfl⟩

theorem actual_closure_binding :
    sentence (Semiformula.univCl (LO.FirstOrder.Arithmetic.succInd nestedSource))ᴺ =
      Formula.closeN (LO.FirstOrder.Arithmetic.succInd nestedSource).fvSup
        (formula (LO.FirstOrder.Arithmetic.succInd nestedSource)ᴺ) :=
  sentence_univCl _

#print axioms hole_substitution
#print axioms successor_substitution
#print axioms add_one_replacement
#print axioms formula_subst_same
#print axioms translated_zero
#print axioms translated_add_one
#print axioms translated_free
#print axioms translated_all
#print axioms translated_imp_elim
#print axioms source_succInd
#print axioms succInd_open
#print axioms succInd_closed
#print axioms induction_axiom
#print axioms literal_zero_slots
#print axioms literal_succ_slots
#print axioms literal_add_one_slots
#print axioms literal_hole_slots
#print axioms zero_really_removes_parameter_slot
#print axioms succ_really_preserves_parameter_slot
#print axioms nested_open_replacement
#print axioms nested_replacement_imp
#print axioms source_zero_binding
#print axioms source_step_binding
#print axioms substitution_with_free_parameter
#print axioms actual_curried_source
#print axioms actual_nested_open
#print axioms actual_nested_closed
#print axioms actual_sparse_closed
#print axioms actual_closure_binding

end DiophantineConsistency.FoundationHAInductionChecks
