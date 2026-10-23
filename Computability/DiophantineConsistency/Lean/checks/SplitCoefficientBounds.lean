import DiophantineConsistency.SplitCoefficientBounds

open DiophantineConsistency.SplitCoefficientBounds
open DiophantineConsistency.SelectiveQuadraticCoding
open Polynomial
open scoped BigOperators

/-- Every coordinate has the same label: the bound permits all collisions. -/
private def weights : Fin 31 → ℕ := fun _ => 0
private def ones : Fin 31 → ℕ := fun _ => 1

private theorem encoded_ones : encoded weights (fun _ => (1:ℤ))=(31:ℤ[X]) := by
  simp [encoded,weights,Polynomial.monomial_zero_left]

private theorem encoded_negative : encoded weights (fun _ => (-1:ℤ))=(-31:ℤ[X]) := by
  simp [encoded,weights,Polynomial.monomial_zero_left]

/-- The factor 993 is attained, so it is not an arbitrary overestimate. -/
example : (product weights (fun _ => (1:ℤ)) 1 1 1).coeff 0=993 := by
  rw [product,encoded_ones]
  norm_num

/-- Signed coordinates and kernels are controlled by the same absolute bound. -/
example : |(product weights (fun _ => (-1:ℤ)) (-1) 1 (-1)).coeff 0|=993 := by
  rw [product,encoded_negative]
  norm_num

/-- The minimal positive digit cap b=1 is admitted by the quarter-base result. -/
example (n : ℕ) : |(product weights (fun _ => (1:ℤ)) 1 1 1).coeff n|<(2:ℤ)^10 := by
  have hD : ∀ i,|(1:ℤ[X]).coeff i|≤(1:ℤ) := by intro i; simp only [coeff_one]; split_ifs <;> norm_num
  have h := quarter_base_bound_31 (y:=ones) weights 1 1 1 (H:=1) (by decide)
    hD hD hD (b:=1) (t:=12) (by decide) (by decide) (by intro i; rfl) (by decide) n
  exact h

/-- Rounding the source base upward also preserves the strict bound. -/
example (n : ℕ) : |(product weights (fun _ => (1:ℤ)) 1 1 1).coeff n|<(2:ℤ)^13/4 := by
  have hD : ∀ i,|(1:ℤ[X]).coeff i|≤(1:ℤ) := by intro i; simp only [coeff_one]; split_ifs <;> norm_num
  exact quarter_base_div_bound_31 (y:=ones) weights 1 1 1 (H:=1) (by decide)
    hD hD hD (b:=1) (t:=13) (by decide) (by decide) (by intro i; rfl) (by decide) n

#print axioms abs_coeff_linear_mul_le
#print axioms abs_coeff_product_le
#print axioms abs_coeff_bounded_nat_le
#print axioms abs_coeff_bounded_nat_le_31
#print axioms quarter_base_bound_31
#print axioms quarter_base_div_bound_31
