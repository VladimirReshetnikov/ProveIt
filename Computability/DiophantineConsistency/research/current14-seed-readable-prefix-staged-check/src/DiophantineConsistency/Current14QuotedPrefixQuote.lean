import DiophantineConsistency.Current14QuotedPrefixCore

/-! SOURCE ONLY. Staged from the independently reviewed prefix draft. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Current14QuotedPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open ObjectCurrentEquation2011 IPRAStandardTheory IPRACurrentNativeZFC
open IPRAFoundationZFCMappedNegation Sign17LinesCurrent14Endpoint
open Sign17ReadableCurrent14Endpoint

/-- Independently transcribed from the page; whitespace is represented by token boundaries. -/
def quoted : List (List String) := [
  ["b", "=", "*", "beta", "J"],
  ["q", "=", "+", "b", "1"],
  ["C", "=", "-", "-", "q", "F", "alpha"],
  ["X", "=", "*", "w", "q"],
  ["Y", "=", "*", "s", "cube", "q"],
  ["E", "=", "*", "X", "Y"],
  ["k", "=", "+", "eta", "zeta"],
  ["ell", "=", "*", "*", "E", "k", "Y"],
  ["c", "=", "+", "*", "k", "Y", "eta"],
  ["a", "=", "+", "E", "Y"],
  ["H", "=", "+", "*", "4", "a", "3"],
  ["Delta", "=", "+", "sq", "a", "H"],
  ["D", "=", "+", "+", "X", "*", "a", "c", "*", "gamma", "H"],
  ["R", "=", "+", "*", "+", "*", "b", "-", "q", "F", "alpha", "-", "sq", "q", "1", "*", "+", "mu", "*", "q", "omega", "J"],
  ["tau", "=", "-", "+", "*", "E", "n", "k", "R"],
  ["V", "=", "-", "*", "sq", "f", "-", "*", "c", "T", "R", "c"],
  ["P", "=", "-", "sq", "tau", "*", "ell", "+", "ell", "k"],
  ["Q", "=", "-", "sq", "D", "*", "Delta", "sq", "c"],
  ["S", "=", "*", "*", "i", "Delta", "sq", "c"],
  ["U", "=", "+", "*", "sq", "S", "-", "sq", "V", "sq", "y", "sq", "y"],
  ["W", "=", "-", "+", "*", "+", "K", "w", "C", "-", "q", "F", "*", "z", "b"],
  ["Z", "=", "-", "*", "Delta", "sq", "f", "sq", "S"],
  ["result", "=", "-", "*", "*", "*", "*", "P", "Q", "U", "W", "Z", "Delta"]]

def quotedExpr (p : Fin 4 → ℤ) : Option (Expr (Fin 14)) := do
  let env ← compile (initial p) quoted
  lookup "result" env

theorem reject_reserved (p : Fin 4 → ℤ) : step (initial p) ["+", "=", "1"] = none := by rfl
theorem reject_empty (p : Fin 4 → ℤ) : step (initial p) ["", "=", "1"] = none := by rfl
theorem reject_duplicate (p : Fin 4 → ℤ) :
    step (("b", Expr.var 0) :: initial p) ["b", "=", "1"] = none := by rfl
theorem reject_unknown (p : Fin 4 → ℤ) : step (initial p) ["b", "=", "unknown"] = none := by rfl
theorem reject_trailing (p : Fin 4 → ℤ) : step (initial p) ["b", "=", "J", "F"] = none := by rfl
theorem reject_exhausted (p : Fin 4 → ℤ) : decode (initial p) 0 ["J"] = none := by rfl
theorem reject_malformed (p : Fin 4 → ℤ) : step (initial p) ["b", "J"] = none := by rfl

theorem quotedExpr_eq (p : Fin 4 → ℤ) :
    quotedExpr p = some (displayedExpr p) := by
  rfl

end DiophantineConsistency.Current14QuotedPrefix
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_reserved
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_empty
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_duplicate
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_unknown
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_trailing
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_exhausted
#print axioms DiophantineConsistency.Current14QuotedPrefix.reject_malformed
#print axioms DiophantineConsistency.Current14QuotedPrefix.quotedExpr_eq
