import DiophantineConsistency.Current14Carrier65DiagonalBase
import DiophantineConsistency.Carrier65

/-! Candidate binding of the generic base degrees to the actual all-equal axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalBinding
open Sign17UnivariateDegree

def axisVars (_ : Fin 14) : P := Polynomial.X
def axisCore (p : Fin 4 → ℤ) : Carrier65.Core P :=
  Carrier65.core (fun j => Polynomial.C (p j)) axisVars

theorem q_eq (p : Fin 4 → ℤ) :
    (axisCore p).q = Current14Carrier65DiagonalBase.q (p 0) := by rfl
theorem X_eq (p : Fin 4 → ℤ) :
    (axisCore p).X = Current14Carrier65DiagonalBase.x (p 0) := by rfl
theorem Y_eq (p : Fin 4 → ℤ) :
    (axisCore p).Y = Current14Carrier65DiagonalBase.y (p 0) := by rfl
theorem E_eq (p : Fin 4 → ℤ) :
    (axisCore p).E = Current14Carrier65DiagonalBase.e (p 0) := by rfl

theorem q_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).q.natDegree = 1 := by
  rw [q_eq]; exact Current14Carrier65DiagonalBase.q_degree (p 0) hp
theorem X_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).X.natDegree = 2 := by
  rw [X_eq]; exact Current14Carrier65DiagonalBase.x_degree (p 0) hp
theorem Y_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).Y.natDegree = 4 := by
  rw [Y_eq]; exact Current14Carrier65DiagonalBase.y_degree (p 0) hp
theorem E_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).E.natDegree = 6 := by
  rw [E_eq]; exact Current14Carrier65DiagonalBase.e_degree (p 0) hp

end DiophantineConsistency.Current14Carrier65DiagonalBinding

#print axioms DiophantineConsistency.Current14Carrier65DiagonalBinding.q_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalBinding.X_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalBinding.Y_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalBinding.E_degree
