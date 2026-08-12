import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def row146ProductMonomials : List Exponent := [
  ![2,1,1,1,1,1],
  ![2,2,0,1,1,1],
  ![2,2,1,0,1,1],
  ![2,2,1,1,0,1],
  ![2,2,1,1,1,0],
  ![3,1,0,1,1,1],
  ![3,1,1,0,1,1],
  ![3,1,1,1,0,1],
  ![3,1,1,1,1,0],
  ![3,2,0,0,1,1],
  ![3,2,0,1,0,1],
  ![3,2,0,1,1,0],
  ![3,2,1,0,0,1],
  ![3,2,1,0,1,0],
  ![3,2,1,1,0,0],
  ![1,0,1,1,1,3],
  ![1,1,0,1,1,3],
  ![1,1,1,0,1,3],
  ![1,1,1,1,0,3],
  ![1,1,1,1,1,2],
  ![2,0,0,1,1,3],
  ![2,0,1,0,1,3],
  ![2,0,1,1,0,3],
  ![2,0,1,1,1,2],
  ![2,1,0,0,1,3],
  ![2,1,0,1,0,3],
  ![2,1,0,1,1,2],
  ![2,1,1,0,0,3],
  ![2,1,1,0,1,2],
  ![2,1,1,1,0,2],
  ![0,0,1,1,3,2],
  ![0,1,0,1,3,2],
  ![0,1,1,0,3,2],
  ![0,1,1,1,2,2],
  ![0,1,1,1,3,1],
  ![1,0,0,1,3,2],
  ![1,0,1,0,3,2],
  ![1,0,1,1,2,2],
  ![1,0,1,1,3,1],
  ![1,1,0,0,3,2],
  ![1,1,0,1,2,2],
  ![1,1,0,1,3,1],
  ![1,1,1,0,2,2],
  ![1,1,1,0,3,1],
  ![1,1,1,1,2,1],
  ![0,0,1,3,2,1],
  ![0,1,0,3,2,1],
  ![0,1,1,2,2,1],
  ![0,1,1,3,1,1],
  ![0,1,1,3,2,0],
  ![1,0,0,3,2,1],
  ![1,0,1,2,2,1],
  ![1,0,1,3,1,1],
  ![1,0,1,3,2,0],
  ![1,1,0,2,2,1],
  ![1,1,0,3,1,1],
  ![1,1,0,3,2,0],
  ![1,1,1,2,1,1],
  ![1,1,1,2,2,0],
  ![1,1,1,3,1,0],
  ![0,0,3,2,1,1],
  ![0,1,2,2,1,1],
  ![0,1,3,1,1,1],
  ![0,1,3,2,0,1],
  ![0,1,3,2,1,0],
  ![1,0,2,2,1,1],
  ![1,0,3,1,1,1],
  ![1,0,3,2,0,1],
  ![1,0,3,2,1,0],
  ![1,1,2,1,1,1],
  ![1,1,2,2,0,1],
  ![1,1,2,2,1,0],
  ![1,1,3,1,0,1],
  ![1,1,3,1,1,0],
  ![1,1,3,2,0,0],
  ![0,2,2,1,1,1],
  ![0,3,1,1,1,1],
  ![0,3,2,0,1,1],
  ![0,3,2,1,0,1],
  ![0,3,2,1,1,0],
  ![1,2,1,1,1,1],
  ![1,2,2,0,1,1],
  ![1,2,2,1,0,1],
  ![1,2,2,1,1,0],
  ![1,3,1,0,1,1],
  ![1,3,1,1,0,1],
  ![1,3,1,1,1,0],
  ![1,3,2,0,0,1],
  ![1,3,2,0,1,0],
  ![1,3,2,1,0,0]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146ProductMonomials_eq_chunked :
    productMonomials (degreeSevenProductSource ⟨146, by decide⟩).2
      (degreeSevenProductSource ⟨146, by decide⟩).1 =
      row146ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk0 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨0 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨0 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk1 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨12 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨12 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk2 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨24 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨24 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk3 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨36 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨36 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk4 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨48 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨48 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk5 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨60 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨60 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk6 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨72 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨72 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk7 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨84 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨84 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk8 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨96 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨96 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk9 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨108 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨108 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row146_product_coefficients_chunk10 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨146, by decide⟩ ⟨120 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨120 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row146ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem row146_product_coefficients_reconstructed :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨146, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative j) := by
  intro j
  generalize hqdef : j.1 / 12 = q
  generalize hrdef : j.1 % 12 = r
  have hq : q < 11 := by
    rw [← hqdef]
    omega
  have hr : r < 12 := by
    rw [← hrdef]
    exact Nat.mod_lt _ (by decide)
  have hj : j = ⟨q * 12 + r, by omega⟩ := by
    apply Fin.ext
    simp only [← hqdef, ← hrdef]
    exact (Nat.div_add_mod' j.1 12).symm
  have hchunk :
      degreeSevenProductRow ⟨146, by decide⟩ ⟨q * 12 + r, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨146, by decide⟩).2
          (degreeSevenProductSource ⟨146, by decide⟩).1
          (degreeSevenRepresentative ⟨q * 12 + r, by omega⟩) := by
    interval_cases q <;>
      first
      | simpa using row146_product_coefficients_chunk0 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk1 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk2 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk3 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk4 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk5 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk6 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk7 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk8 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk9 ⟨r, hr⟩
      | simpa using row146_product_coefficients_chunk10 ⟨r, hr⟩
  simpa [hj] using hchunk

theorem row146_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨146, by decide⟩ =
      degreeSevenEncodedProduct ⟨146, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row146_product_coefficients_reconstructed

def row147ProductMonomials : List Exponent := [
  ![1,0,3,1,1,1],
  ![1,1,2,1,1,1],
  ![1,1,3,0,1,1],
  ![1,1,3,1,0,1],
  ![1,1,3,1,1,0],
  ![2,0,2,1,1,1],
  ![2,0,3,0,1,1],
  ![2,0,3,1,0,1],
  ![2,0,3,1,1,0],
  ![2,1,2,0,1,1],
  ![2,1,2,1,0,1],
  ![2,1,2,1,1,0],
  ![2,1,3,0,0,1],
  ![2,1,3,0,1,0],
  ![2,1,3,1,0,0],
  ![0,2,1,1,1,2],
  ![0,3,0,1,1,2],
  ![0,3,1,0,1,2],
  ![0,3,1,1,0,2],
  ![0,3,1,1,1,1],
  ![1,2,0,1,1,2],
  ![1,2,1,0,1,2],
  ![1,2,1,1,0,2],
  ![1,2,1,1,1,1],
  ![1,3,0,0,1,2],
  ![1,3,0,1,0,2],
  ![1,3,0,1,1,1],
  ![1,3,1,0,0,2],
  ![1,3,1,0,1,1],
  ![1,3,1,1,0,1],
  ![2,0,1,1,2,1],
  ![2,1,0,1,2,1],
  ![2,1,1,0,2,1],
  ![2,1,1,1,1,1],
  ![2,1,1,1,2,0],
  ![3,0,0,1,2,1],
  ![3,0,1,0,2,1],
  ![3,0,1,1,1,1],
  ![3,0,1,1,2,0],
  ![3,1,0,0,2,1],
  ![3,1,0,1,1,1],
  ![3,1,0,1,2,0],
  ![3,1,1,0,1,1],
  ![3,1,1,0,2,0],
  ![3,1,1,1,1,0],
  ![0,0,1,2,1,3],
  ![0,1,0,2,1,3],
  ![0,1,1,1,1,3],
  ![0,1,1,2,0,3],
  ![0,1,1,2,1,2],
  ![1,0,0,2,1,3],
  ![1,0,1,1,1,3],
  ![1,0,1,2,0,3],
  ![1,0,1,2,1,2],
  ![1,1,0,1,1,3],
  ![1,1,0,2,0,3],
  ![1,1,0,2,1,2],
  ![1,1,1,1,0,3],
  ![1,1,1,1,1,2],
  ![1,1,1,2,0,2],
  ![0,0,2,1,3,1],
  ![0,1,1,1,3,1],
  ![0,1,2,0,3,1],
  ![0,1,2,1,2,1],
  ![0,1,2,1,3,0],
  ![1,0,1,1,3,1],
  ![1,0,2,0,3,1],
  ![1,0,2,1,2,1],
  ![1,0,2,1,3,0],
  ![1,1,1,0,3,1],
  ![1,1,1,1,2,1],
  ![1,1,1,1,3,0],
  ![1,1,2,0,2,1],
  ![1,1,2,0,3,0],
  ![1,1,2,1,2,0],
  ![0,1,1,3,1,1],
  ![0,2,0,3,1,1],
  ![0,2,1,2,1,1],
  ![0,2,1,3,0,1],
  ![0,2,1,3,1,0],
  ![1,1,0,3,1,1],
  ![1,1,1,2,1,1],
  ![1,1,1,3,0,1],
  ![1,1,1,3,1,0],
  ![1,2,0,2,1,1],
  ![1,2,0,3,0,1],
  ![1,2,0,3,1,0],
  ![1,2,1,2,0,1],
  ![1,2,1,2,1,0],
  ![1,2,1,3,0,0]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147ProductMonomials_eq_chunked :
    productMonomials (degreeSevenProductSource ⟨147, by decide⟩).2
      (degreeSevenProductSource ⟨147, by decide⟩).1 =
      row147ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk0 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨0 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨0 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk1 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨12 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨12 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk2 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨24 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨24 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk3 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨36 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨36 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk4 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨48 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨48 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk5 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨60 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨60 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk6 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨72 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨72 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk7 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨84 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨84 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk8 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨96 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨96 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk9 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨108 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨108 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row147_product_coefficients_chunk10 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨147, by decide⟩ ⟨120 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨120 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row147ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem row147_product_coefficients_reconstructed :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨147, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative j) := by
  intro j
  generalize hqdef : j.1 / 12 = q
  generalize hrdef : j.1 % 12 = r
  have hq : q < 11 := by
    rw [← hqdef]
    omega
  have hr : r < 12 := by
    rw [← hrdef]
    exact Nat.mod_lt _ (by decide)
  have hj : j = ⟨q * 12 + r, by omega⟩ := by
    apply Fin.ext
    simp only [← hqdef, ← hrdef]
    exact (Nat.div_add_mod' j.1 12).symm
  have hchunk :
      degreeSevenProductRow ⟨147, by decide⟩ ⟨q * 12 + r, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨147, by decide⟩).2
          (degreeSevenProductSource ⟨147, by decide⟩).1
          (degreeSevenRepresentative ⟨q * 12 + r, by omega⟩) := by
    interval_cases q <;>
      first
      | simpa using row147_product_coefficients_chunk0 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk1 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk2 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk3 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk4 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk5 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk6 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk7 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk8 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk9 ⟨r, hr⟩
      | simpa using row147_product_coefficients_chunk10 ⟨r, hr⟩
  simpa [hj] using hchunk

theorem row147_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨147, by decide⟩ =
      degreeSevenEncodedProduct ⟨147, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row147_product_coefficients_reconstructed

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
