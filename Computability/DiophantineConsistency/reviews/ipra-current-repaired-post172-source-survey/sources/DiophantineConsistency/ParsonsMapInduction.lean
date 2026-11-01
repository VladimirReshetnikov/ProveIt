import DiophantineConsistency.PRALanguage
import Foundation.FirstOrder.Arithmetic.Schemata
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsMapInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage

theorem map_zero {n : ℕ} : Semiterm.lMap embedding (‘0’ : SyntacticSemiterm ℒₒᵣ n) = (‘0’ : SyntacticSemiterm language n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, PRALanguage.embedding, Language.ORing.embedding]

theorem map_add_one {n : ℕ} :
    Semiterm.lMap embedding (‘(#0 + 1)’ : SyntacticSemiterm ℒₒᵣ (n+1)) =
      (‘(#0 + 1)’ : SyntacticSemiterm language (n+1)) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq,
    PRALanguage.embedding, Language.ORing.embedding]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Function.comp_def]
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def]
    funext x
    exact Fin.elim0 x

theorem map_succInd (φ : ArithmeticSemiformula ℕ 1) :
    Semiformula.lMap embedding (succInd φ) = succInd (Semiformula.lMap embedding φ) := by
  simp [succInd, Semiformula.lMap_subst, map_zero, map_add_one]
end DiophantineConsistency.ParsonsMapInduction
