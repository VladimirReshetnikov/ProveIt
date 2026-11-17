import IPRADerivations.Algebra.CayleyHamiltonGeneral

/-!
# The principal-minor formula

Packet: `cayley_hamilton_ipra`, `sections/trace.tex`, Proposition `prop:trace-principal`: the coefficient
`e_k` of `t^k` in `det(I + tA)` is the sum of the `k × k` principal minors,
`e_k = ∑_{|S| = k} det A[S, S]`; in particular `e_1 = tr A` and `e_n = det A`.

* `ekZ M k`: the sum of the principal minors, an explicit iPRA term (each minor a `Mat.det` term);
* `toZ_ekZ`: it evaluates to the coefficient of `t^k` in `det(I + tA)` (Mathlib's
  `coeff_det_one_add_X_smul_eq_sum_minors`), which is how the packet defines `e_k`;
* `cfZ_eq`: the characteristic coefficients of `Algebra/CayleyHamiltonGeneral` are `(−1)^k e_k`;
* `e_one`, `e_top` (iPRA theorems): `e_1 = tr M` and `e_m = det M`, for every fixed size `m`.
-/

namespace LeanProofs.IPRA.Algebra.PrincipalMinors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CayleyHamiltonGeneral
open Matrix Polynomial
open scoped Fm

variable {n m : ℕ} {Γ : List (Fm PTm n)}

/-- `e_k = ∑_{|S| = k} det M[S, S]`. -/
noncomputable def ekZ (M : Mat m n) (k : ℕ) : ZT n :=
  zsumL (((Finset.univ : Finset (Fin m)).powersetCard k).toList.map (minorZ M))

theorem cfZ_eq (M : Mat m n) (k : ℕ) : cfZ M k = ZT.signPow k (ekZ M k) := rfl

/-- `e_k` is the coefficient of `t^k` in `det(I + tA)`. -/
theorem toZ_ekZ (M : Mat m n) (k : ℕ) :
    ZT.toZ Γ (ekZ M k) = (det (1 + (X : (Groth (Q Γ))[X]) • (Mat.toZ Γ M).map C)).coeff k := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors, ekZ, toZ_zsumL, List.map_map, ← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro s _
  simp [toZ_minorZ]

/-- `e_1 = tr M`. -/
theorem e_one (M : Mat m n) : Γ ⊢[PRAAx] ZT.eq (ekZ M 1) (Mat.trace M) :=
  ZT.derive (by rw [toZ_ekZ, Matrix.coeff_det_one_add_X_smul_one, Mat.toZ_trace])

/-- `e_m = det M`. -/
theorem e_top (M : Mat m n) : Γ ⊢[PRAAx] ZT.eq (ekZ M m) (Mat.det M) := by
  refine ZT.derive ?_
  have c := toZ_cfZ (Γ := Γ) M (le_refl m)
  rw [cfZ_eq, ZT.toZ_signPow, Nat.sub_self] at c
  have d := Matrix.det_eq_sign_charpoly_coeff (Mat.toZ Γ M)
  rw [Fintype.card_fin, ← c, ← _root_.mul_assoc, ← _root_.pow_add, ← _root_.two_mul, _root_.pow_mul] at d
  rw [Mat.toZ_det, d]
  simp

end LeanProofs.IPRA.Algebra.PrincipalMinors
