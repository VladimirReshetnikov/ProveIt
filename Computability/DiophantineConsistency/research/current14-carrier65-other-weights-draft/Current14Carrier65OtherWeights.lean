import DiophantineConsistency.Current14Carrier65QInputs

/-! Candidate syntactic degree weights for all non-Q factors. -/
namespace DiophantineConsistency.Current14Carrier65OtherWeights
open Current14Carrier65QInputs

def b (p : Fin 4 → ℤ) : Expr (Fin 14) := Expr.constant (p 0) * .var 0
def C (p : Fin 4 → ℤ) : Expr (Fin 14) := q p - .var 1 - .var 2
def delta (p : Fin 4 → ℤ) : Expr (Fin 14) := a p ^ 2 + H p
def ell (p : Fin 4 → ℤ) : Expr (Fin 14) := E p * k * Y p
def rank (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  (b p * (q p - .var 1) + .var 2) * (q p ^ 2 - 1) +
    (Expr.constant (p 2) + q p * Expr.constant (p 3)) * .var 0
def tau (p : Fin 4 → ℤ) : Expr (Fin 14) := E p * .var 9 + k - rank p
def V (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 4 ^ 2 * (c p * .var 6 - rank p) - c p
def S (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 5 * delta p * c p ^ 2
def P (p : Fin 4 → ℤ) : Expr (Fin 14) := tau p ^ 2 - ell p * (ell p + k)
def U (p : Fin 4 → ℤ) : Expr (Fin 14) := S p ^ 2 * (V p ^ 2 - .var 12 ^ 2) + .var 12 ^ 2
def W (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  (Expr.constant (p 1) + .var 8) * C p + (q p - .var 1) - .var 3 * b p
def Z (p : Fin 4 → ℤ) : Expr (Fin 14) := delta p * .var 4 ^ 2 - S p ^ 2

theorem delta_weight (p : Fin 4 → ℤ) : (delta p).weightedDegree weight = 12 := by rfl
theorem rank_weight (p : Fin 4 → ℤ) : (rank p).weightedDegree weight = 4 := by rfl
theorem tau_weight (p : Fin 4 → ℤ) : (tau p).weightedDegree weight = 7 := by rfl
theorem V_weight (p : Fin 4 → ℤ) : (V p).weightedDegree weight = 8 := by rfl
theorem S_weight (p : Fin 4 → ℤ) : (S p).weightedDegree weight = 23 := by rfl
theorem P_weight (p : Fin 4 → ℤ) : (P p).weightedDegree weight = 22 := by rfl
theorem U_weight (p : Fin 4 → ℤ) : (U p).weightedDegree weight = 62 := by rfl
theorem W_weight (p : Fin 4 → ℤ) : (W p).weightedDegree weight = 2 := by rfl
theorem Z_weight (p : Fin 4 → ℤ) : (Z p).weightedDegree weight = 46 := by rfl

end DiophantineConsistency.Current14Carrier65OtherWeights

#print axioms DiophantineConsistency.Current14Carrier65OtherWeights.delta_weight
#print axioms DiophantineConsistency.Current14Carrier65OtherWeights.P_weight
#print axioms DiophantineConsistency.Current14Carrier65OtherWeights.U_weight
#print axioms DiophantineConsistency.Current14Carrier65OtherWeights.W_weight
#print axioms DiophantineConsistency.Current14Carrier65OtherWeights.Z_weight
