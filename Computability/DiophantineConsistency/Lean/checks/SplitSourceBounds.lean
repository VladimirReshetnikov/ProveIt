import DiophantineConsistency.SplitSourceBounds

open DiophantineConsistency.SplitSourceBounds
open DiophantineConsistency.SplitCoefficientBounds
open DiophantineConsistency.SelectiveQuadraticCoding
open Polynomial

/-- A single top-position digit attains the highest permitted degree. -/
example : product (fun _ : Fin 1 => 116) (fun _ => (1:ℤ)) 0 0 (X^1929)=X^2161 := by
  simp [product,encoded,← C_mul_X_pow_eq_monomial,← pow_mul,← pow_add]

example : (product (fun _ : Fin 1 => 116) (fun _ => (1:ℤ)) 0 0 (X^1929)).natDegree=2161 := by
  have he : product (fun _ : Fin 1 => 116) (fun _ => (1:ℤ)) 0 0 (X^1929)=X^2161 := by
    simp [product,encoded,← C_mul_X_pow_eq_monomial,← pow_mul,← pow_add]
  rw [he]
  simp

/-- Zero coefficients and cancellations do not require a nonzero hypothesis. -/
example (w : Fin 31 → ℕ) (hw : ∀ i,w i≤116) :
    (product w (fun _ => (0:ℤ)) 0 0 0).natDegree≤2161 := by
  exact product_natDegree_le (d0:=1719) (d1:=2027) (d2:=1929) w hw
    (fun _ => 0) 0 0 0 (by simp) (by simp) (by simp)

#print axioms encoded_natDegree_le
#print axioms product_natDegree_le
#print axioms product_natDegree_le_2161
#print axioms product_natDegree_lt_2162
