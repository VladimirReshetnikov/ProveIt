import DiophantineConsistency.Current14Carrier65DiagonalBinding
import DiophantineConsistency.Current14Carrier65DiagonalCore

/-! Candidate c/a/H/delta binding on the actual all-equal axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalCoreBinding
open Sign17UnivariateDegree Current14Carrier65DiagonalBinding

theorem c_eq (p : Fin 4 → ℤ) :
    (axisCore p).c = Current14Carrier65DiagonalCore.c (p 0) := by
  change (Polynomial.X + Polynomial.X) * Current14Carrier65DiagonalBase.y (p 0) + Polynomial.X =
    (Polynomial.C (2 : ℤ) * Polynomial.X) * Current14Carrier65DiagonalBase.y (p 0) + Polynomial.X
  simp only [map_ofNat, two_mul]

theorem a_eq (p : Fin 4 → ℤ) :
    (axisCore p).a = Current14Carrier65DiagonalCore.a (p 0) := by rfl

theorem H_eq (p : Fin 4 → ℤ) :
    (axisCore p).H = Current14Carrier65DiagonalCore.H (p 0) := by
  change 4 * (axisCore p).a + 3 = Polynomial.C (4 : ℤ) *
    Current14Carrier65DiagonalCore.a (p 0) + 3
  rw [a_eq]
  simp only [map_ofNat]

theorem delta_eq (p : Fin 4 → ℤ) :
    (axisCore p).delta = Current14Carrier65DiagonalCore.delta (p 0) := by
  change (axisCore p).a ^ 2 + (axisCore p).H = _
  rw [a_eq, H_eq]
  rfl

theorem c_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).c.natDegree = 5 := by
  rw [c_eq]; exact Current14Carrier65DiagonalCore.c_degree (p 0) hp
theorem a_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).a.natDegree = 6 := by
  rw [a_eq]; exact Current14Carrier65DiagonalCore.a_degree (p 0) hp
theorem H_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).H.natDegree = 6 := by
  rw [H_eq]; exact Current14Carrier65DiagonalCore.H_degree (p 0) hp
theorem delta_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).delta.natDegree = 12 := by
  rw [delta_eq]; exact Current14Carrier65DiagonalCore.delta_degree (p 0) hp

end DiophantineConsistency.Current14Carrier65DiagonalCoreBinding

#print axioms DiophantineConsistency.Current14Carrier65DiagonalCoreBinding.c_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalCoreBinding.a_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalCoreBinding.H_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalCoreBinding.delta_degree
