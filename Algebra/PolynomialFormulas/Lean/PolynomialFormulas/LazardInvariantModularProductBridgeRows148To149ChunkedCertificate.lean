import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def row148ProductMonomials : List Exponent := [
  ![1,1,2,1,1,1],
  ![1,2,1,1,1,1],
  ![1,2,2,0,1,1],
  ![1,2,2,1,0,1],
  ![1,2,2,1,1,0],
  ![2,1,1,1,1,1],
  ![2,1,2,0,1,1],
  ![2,1,2,1,0,1],
  ![2,1,2,1,1,0],
  ![2,2,1,0,1,1],
  ![2,2,1,1,0,1],
  ![2,2,1,1,1,0],
  ![2,2,2,0,0,1],
  ![2,2,2,0,1,0],
  ![2,2,2,1,0,0],
  ![1,1,1,1,1,2],
  ![1,2,0,1,1,2],
  ![1,2,1,0,1,2],
  ![1,2,1,1,0,2],
  ![1,2,1,1,1,1],
  ![2,1,0,1,1,2],
  ![2,1,1,0,1,2],
  ![2,1,1,1,0,2],
  ![2,1,1,1,1,1],
  ![2,2,0,0,1,2],
  ![2,2,0,1,0,2],
  ![2,2,0,1,1,1],
  ![2,2,1,0,0,2],
  ![2,2,1,0,1,1],
  ![2,2,1,1,0,1],
  ![1,0,1,1,2,2],
  ![1,1,0,1,2,2],
  ![1,1,1,0,2,2],
  ![1,1,1,1,1,2],
  ![1,1,1,1,2,1],
  ![2,0,0,1,2,2],
  ![2,0,1,0,2,2],
  ![2,0,1,1,1,2],
  ![2,0,1,1,2,1],
  ![2,1,0,0,2,2],
  ![2,1,0,1,1,2],
  ![2,1,0,1,2,1],
  ![2,1,1,0,1,2],
  ![2,1,1,0,2,1],
  ![2,1,1,1,1,1],
  ![0,0,1,2,2,2],
  ![0,1,0,2,2,2],
  ![0,1,1,1,2,2],
  ![0,1,1,2,1,2],
  ![0,1,1,2,2,1],
  ![1,0,0,2,2,2],
  ![1,0,1,1,2,2],
  ![1,0,1,2,1,2],
  ![1,0,1,2,2,1],
  ![1,1,0,1,2,2],
  ![1,1,0,2,1,2],
  ![1,1,0,2,2,1],
  ![1,1,1,1,1,2],
  ![1,1,1,1,2,1],
  ![1,1,1,2,1,1],
  ![0,0,2,2,2,1],
  ![0,1,1,2,2,1],
  ![0,1,2,1,2,1],
  ![0,1,2,2,1,1],
  ![0,1,2,2,2,0],
  ![1,0,1,2,2,1],
  ![1,0,2,1,2,1],
  ![1,0,2,2,1,1],
  ![1,0,2,2,2,0],
  ![1,1,1,1,2,1],
  ![1,1,1,2,1,1],
  ![1,1,1,2,2,0],
  ![1,1,2,1,1,1],
  ![1,1,2,1,2,0],
  ![1,1,2,2,1,0],
  ![0,1,2,2,1,1],
  ![0,2,1,2,1,1],
  ![0,2,2,1,1,1],
  ![0,2,2,2,0,1],
  ![0,2,2,2,1,0],
  ![1,1,1,2,1,1],
  ![1,1,2,1,1,1],
  ![1,1,2,2,0,1],
  ![1,1,2,2,1,0],
  ![1,2,1,1,1,1],
  ![1,2,1,2,0,1],
  ![1,2,1,2,1,0],
  ![1,2,2,1,0,1],
  ![1,2,2,1,1,0],
  ![1,2,2,2,0,0]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148ProductMonomials_eq_chunked :
    productMonomials (degreeSevenProductSource ⟨148, by decide⟩).2
      (degreeSevenProductSource ⟨148, by decide⟩).1 =
      row148ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk0 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨0 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨0 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk1 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨12 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨12 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk2 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨24 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨24 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk3 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨36 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨36 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk4 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨48 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨48 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk5 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨60 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨60 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk6 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨72 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨72 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk7 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨84 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨84 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk8 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨96 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨96 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk9 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨108 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨108 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row148_product_coefficients_chunk10 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨148, by decide⟩ ⟨120 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨120 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row148ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem row148_product_coefficients_reconstructed :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨148, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
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
      degreeSevenProductRow ⟨148, by decide⟩ ⟨q * 12 + r, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨148, by decide⟩).2
          (degreeSevenProductSource ⟨148, by decide⟩).1
          (degreeSevenRepresentative ⟨q * 12 + r, by omega⟩) := by
    interval_cases q <;>
      first
      | simpa using row148_product_coefficients_chunk0 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk1 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk2 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk3 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk4 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk5 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk6 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk7 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk8 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk9 ⟨r, hr⟩
      | simpa using row148_product_coefficients_chunk10 ⟨r, hr⟩
  simpa [hj] using hchunk

theorem row148_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨148, by decide⟩ =
      degreeSevenEncodedProduct ⟨148, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row148_product_coefficients_reconstructed

def row149ProductMonomials : List Exponent := [
  ![2,0,2,1,1,1],
  ![2,1,1,1,1,1],
  ![2,1,2,0,1,1],
  ![2,1,2,1,0,1],
  ![2,1,2,1,1,0],
  ![3,0,1,1,1,1],
  ![3,0,2,0,1,1],
  ![3,0,2,1,0,1],
  ![3,0,2,1,1,0],
  ![3,1,1,0,1,1],
  ![3,1,1,1,0,1],
  ![3,1,1,1,1,0],
  ![3,1,2,0,0,1],
  ![3,1,2,0,1,0],
  ![3,1,2,1,0,0],
  ![0,1,1,1,1,3],
  ![0,2,0,1,1,3],
  ![0,2,1,0,1,3],
  ![0,2,1,1,0,3],
  ![0,2,1,1,1,2],
  ![1,1,0,1,1,3],
  ![1,1,1,0,1,3],
  ![1,1,1,1,0,3],
  ![1,1,1,1,1,2],
  ![1,2,0,0,1,3],
  ![1,2,0,1,0,3],
  ![1,2,0,1,1,2],
  ![1,2,1,0,0,3],
  ![1,2,1,0,1,2],
  ![1,2,1,1,0,2],
  ![1,0,1,1,3,1],
  ![1,1,0,1,3,1],
  ![1,1,1,0,3,1],
  ![1,1,1,1,2,1],
  ![1,1,1,1,3,0],
  ![2,0,0,1,3,1],
  ![2,0,1,0,3,1],
  ![2,0,1,1,2,1],
  ![2,0,1,1,3,0],
  ![2,1,0,0,3,1],
  ![2,1,0,1,2,1],
  ![2,1,0,1,3,0],
  ![2,1,1,0,2,1],
  ![2,1,1,0,3,0],
  ![2,1,1,1,2,0],
  ![0,0,1,3,1,2],
  ![0,1,0,3,1,2],
  ![0,1,1,2,1,2],
  ![0,1,1,3,0,2],
  ![0,1,1,3,1,1],
  ![1,0,0,3,1,2],
  ![1,0,1,2,1,2],
  ![1,0,1,3,0,2],
  ![1,0,1,3,1,1],
  ![1,1,0,2,1,2],
  ![1,1,0,3,0,2],
  ![1,1,0,3,1,1],
  ![1,1,1,2,0,2],
  ![1,1,1,2,1,1],
  ![1,1,1,3,0,1],
  ![0,0,3,1,2,1],
  ![0,1,2,1,2,1],
  ![0,1,3,0,2,1],
  ![0,1,3,1,1,1],
  ![0,1,3,1,2,0],
  ![1,0,2,1,2,1],
  ![1,0,3,0,2,1],
  ![1,0,3,1,1,1],
  ![1,0,3,1,2,0],
  ![1,1,2,0,2,1],
  ![1,1,2,1,1,1],
  ![1,1,2,1,2,0],
  ![1,1,3,0,1,1],
  ![1,1,3,0,2,0],
  ![1,1,3,1,1,0],
  ![0,2,1,2,1,1],
  ![0,3,0,2,1,1],
  ![0,3,1,1,1,1],
  ![0,3,1,2,0,1],
  ![0,3,1,2,1,0],
  ![1,2,0,2,1,1],
  ![1,2,1,1,1,1],
  ![1,2,1,2,0,1],
  ![1,2,1,2,1,0],
  ![1,3,0,1,1,1],
  ![1,3,0,2,0,1],
  ![1,3,0,2,1,0],
  ![1,3,1,1,0,1],
  ![1,3,1,1,1,0],
  ![1,3,1,2,0,0]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149ProductMonomials_eq_chunked :
    productMonomials (degreeSevenProductSource ⟨149, by decide⟩).2
      (degreeSevenProductSource ⟨149, by decide⟩).1 =
      row149ProductMonomials := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk0 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨0 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨0 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk1 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨12 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨12 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk2 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨24 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨24 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk3 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨36 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨36 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk4 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨48 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨48 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk5 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨60 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨60 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk6 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨72 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨72 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk7 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨84 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨84 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk8 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨96 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨96 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk9 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨108 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨108 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem row149_product_coefficients_chunk10 :
    ∀ j : Fin 12,
      degreeSevenProductRow ⟨149, by decide⟩ ⟨120 + j.1, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨120 + j.1, by omega⟩) := by
  intro j
  unfold productCoefficient
  rw [row149ProductMonomials_eq_chunked]
  revert j
  decide

set_option maxRecDepth 300000 in
set_option maxHeartbeats 80000000 in
theorem row149_product_coefficients_reconstructed :
    ∀ j : Fin 132,
      degreeSevenProductRow ⟨149, by decide⟩ j =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
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
      degreeSevenProductRow ⟨149, by decide⟩ ⟨q * 12 + r, by omega⟩ =
        productCoefficient (degreeSevenProductSource ⟨149, by decide⟩).2
          (degreeSevenProductSource ⟨149, by decide⟩).1
          (degreeSevenRepresentative ⟨q * 12 + r, by omega⟩) := by
    interval_cases q <;>
      first
      | simpa using row149_product_coefficients_chunk0 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk1 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk2 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk3 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk4 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk5 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk6 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk7 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk8 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk9 ⟨r, hr⟩
      | simpa using row149_product_coefficients_chunk10 ⟨r, hr⟩
  simpa [hj] using hchunk

theorem row149_literalProduct_eq_encoded_direct :
    degreeSevenLiteralProduct ⟨149, by decide⟩ =
      degreeSevenEncodedProduct ⟨149, by decide⟩ := by
  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients
  exact row149_product_coefficients_reconstructed

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
