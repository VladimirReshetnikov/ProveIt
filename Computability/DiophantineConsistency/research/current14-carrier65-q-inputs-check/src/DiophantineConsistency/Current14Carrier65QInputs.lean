import DiophantineConsistency.WeightedExpressionDegree

/-! Proposed input syntax bounds for the cancellation-aware Q factor. -/
namespace DiophantineConsistency.Current14Carrier65QInputs

def weight (_ : Fin 14) : ℕ := 1
def q (p : Fin 4 → ℤ) : Expr (Fin 14) := Expr.constant (p 0) * .var 0 + 1
def X (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 8 * q p
def Y (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 7 * q p ^ 3
def E (p : Fin 4 → ℤ) : Expr (Fin 14) := X p * Y p
def k : Expr (Fin 14) := .var 10 + .var 11
def c (p : Fin 4 → ℤ) : Expr (Fin 14) := k * Y p + .var 10
def a (p : Fin 4 → ℤ) : Expr (Fin 14) := E p + Y p
def H (p : Fin 4 → ℤ) : Expr (Fin 14) := 4 * a p + 3

theorem q_weight (p : Fin 4 → ℤ) : (q p).weightedDegree weight = 1 := by decide +kernel
theorem X_weight (p : Fin 4 → ℤ) : (X p).weightedDegree weight = 2 := by decide +kernel
theorem Y_weight (p : Fin 4 → ℤ) : (Y p).weightedDegree weight = 4 := by decide +kernel
theorem E_weight (p : Fin 4 → ℤ) : (E p).weightedDegree weight = 6 := by decide +kernel
theorem c_weight (p : Fin 4 → ℤ) : (c p).weightedDegree weight = 5 := by decide +kernel
theorem a_weight (p : Fin 4 → ℤ) : (a p).weightedDegree weight = 6 := by decide +kernel
theorem H_weight (p : Fin 4 → ℤ) : (H p).weightedDegree weight = 6 := by decide +kernel

end DiophantineConsistency.Current14Carrier65QInputs

#print axioms DiophantineConsistency.Current14Carrier65QInputs.X_weight
#print axioms DiophantineConsistency.Current14Carrier65QInputs.c_weight
#print axioms DiophantineConsistency.Current14Carrier65QInputs.a_weight
#print axioms DiophantineConsistency.Current14Carrier65QInputs.H_weight
