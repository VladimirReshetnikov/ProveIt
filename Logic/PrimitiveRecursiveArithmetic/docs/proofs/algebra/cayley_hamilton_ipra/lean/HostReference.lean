import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
Host-level reference targets for the Cayley--Hamilton packet.

STATUS: source outline, not compiled in the delivery environment.
API names were checked against mathlib tag v4.32.0.

These theorems use existing Mathlib proofs. They are NOT derivations in
the object theory iPRA and do NOT discharge ObjectLanguageTargets.lean.
No assertion of iPRA provability is obtained by importing this file.
-/

noncomputable section

namespace CayleyHamiltonHostReference

open Polynomial

variable {R : Type*} [CommRing R]

theorem cayleyHamilton (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A

theorem polynomialReduction (n : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (p : R[X]) : aeval A p = aeval A (p %ₘ A.charpoly) :=
  Matrix.aeval_eq_aeval_mod_charpoly A p

theorem powerReduction (n : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (k : ℕ) : A ^ k = aeval A (X ^ k %ₘ A.charpoly) :=
  Matrix.pow_eq_aeval_mod_charpoly A k

end CayleyHamiltonHostReference
