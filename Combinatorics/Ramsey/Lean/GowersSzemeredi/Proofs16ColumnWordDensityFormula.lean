import GowersSzemeredi.Proofs16ColumnWordDensity

/-! The cubic density recurrence has a geometric exponent, rather than
an exponent obtained by repeatedly taking the smaller input density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Closed form for the density of a word of `k+1` triples. -/
theorem columnWordDensity_formula (lambda eta : Real) (k : Nat) :
    columnWordDensity lambda eta k =
      (eta^2*lambda^3/64)^(∑ i ∈ Finset.range k, 3^i) * lambda^(3^k) := by
  induction k with
  | zero => simp [columnWordDensity]
  | succ k ih =>
    have hg : (∑ i ∈ Finset.range k, (3 : Nat)^i)*2+1 = 3^k := by
      simpa using geom_sum_mul_add (2 : Nat) k
    have hs : (∑ i ∈ Finset.range k, (3 : Nat)^i)*3+1 =
        (∑ i ∈ Finset.range k, (3 : Nat)^i)+3^k := by omega
    calc columnWordDensity lambda eta (k+1)
        = (eta^2*lambda^3/64)*
            ((eta^2*lambda^3/64)^(∑ i ∈ Finset.range k, 3^i)*lambda^(3^k))^3 := by
              rw [columnWordDensity,ih]; ring
      _ = (eta^2*lambda^3/64)^((∑ i ∈ Finset.range k, 3^i)*3+1)*lambda^(3^k*3) := by
        simp only [pow_succ, mul_pow, pow_mul]; ring
      _ = _ := by rw [Finset.sum_range_succ, hs, pow_succ (3 : Nat) k]

/-- The exponent multiplying the per-step loss is exactly `(3^k-1)/2`. -/
theorem columnWordDensity_loss_exponent (k : Nat) :
    (∑ i ∈ Finset.range k, (3 : Nat)^i) = (3^k-1)/2 := by
  have hg : (∑ i ∈ Finset.range k, (3 : Nat)^i)*2+1 = 3^k := by
    simpa using geom_sum_mul_add (2 : Nat) k
  omega

end LeanProofs.GowersSzemeredi
