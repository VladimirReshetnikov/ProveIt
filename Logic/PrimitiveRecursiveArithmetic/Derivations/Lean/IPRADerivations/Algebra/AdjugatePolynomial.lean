import IPRADerivations.Algebra.CayleyHamiltonGeneral

/-!
# The adjugate as a polynomial in the matrix

Packet: `cayley_hamilton_ipra`, `sections/core.tex`, Theorem `thm:adjpoly`: for `m ≥ 1`,
`adj A = (−1)^{m−1} ∑_{k=1}^{m} c_k A^{k−1}`, where `c_k` is the coefficient of `X^k` in `det(X I − A)`.

* Over every commutative ring (`adj_poly`): Cayley–Hamilton gives `A · S(A) = −c_0 I` for
  `S(A) = ∑_{k<m} c_{k+1} A^k`, and `c_0 = (−1)^m det A`. For the universal matrix of variables over
  `ℤ`, `det` is a nonzero element of an integral domain, so `A (adj A − (−1)^{m−1} S(A)) = 0` can be
  cancelled (`adj_poly_generic`); every matrix is a specialization of it.
* In iPRA (`adjugate_polynomial`): with the explicit coefficient terms `cf` of
  `Algebra/CayleyHamiltonGeneral`, `adj M = (−1)^{m−1} ∑_{k<m} cf M (m − k − 1) · M^k`.
-/

namespace LeanProofs.IPRA.Algebra.AdjugatePolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CayleyHamiltonGeneral
open Matrix Polynomial

section Ring

variable {R : Type*} [CommRing R] {m : ℕ}

noncomputable def Sp (A : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  ∑ k ∈ Finset.range m, A.charpoly.coeff (k + 1) • A ^ k

theorem mul_Sp (A : Matrix (Fin m) (Fin m) R) :
    A * Sp A = -(A.charpoly.coeff 0 • (1 : Matrix (Fin m) (Fin m) R)) := by
  rcases subsingleton_or_nontrivial R with hs | hs
  · exact Subsingleton.elim _ _
  have h := Matrix.aeval_self_charpoly A
  rw [Polynomial.aeval_eq_sum_range' (n := m + 1) (by simp)] at h
  rw [Finset.sum_range_succ'] at h
  rw [Sp, Finset.mul_sum, _root_.eq_neg_iff_add_eq_zero, ← h]
  simp only [_root_.pow_zero, _root_.pow_succ', Matrix.mul_smul]

theorem adj_poly_generic (hm : 1 ≤ m) :
    adjugate (mvPolynomialX (Fin m) (Fin m) ℤ) =
      ((-1) ^ (m - 1) : MvPolynomial (Fin m × Fin m) ℤ) • Sp (mvPolynomialX (Fin m) (Fin m) ℤ) := by
  set X := mvPolynomialX (Fin m) (Fin m) ℤ
  have hd : X.det ≠ 0 := det_mvPolynomialX_ne_zero (m := Fin m) (R := ℤ)
  have e1 : X * adjugate X = X.det • 1 := mul_adjugate X
  have e2 : X * Sp X = -(X.charpoly.coeff 0 • 1) := mul_Sp X
  have hc : X.charpoly.coeff 0 = (-1) ^ m * X.det := by
    have := det_eq_sign_charpoly_coeff X
    rw [Fintype.card_fin] at this
    rw [this, ← _root_.mul_assoc, ← _root_.pow_add, ← _root_.two_mul, _root_.pow_mul]; simp
  have hs : X.det + (-1) ^ (m - 1) * ((-1) ^ m * X.det) = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have a : ((-1 : MvPolynomial (Fin (k + 1) × Fin (k + 1)) ℤ) ^ k) * (-1) ^ k = 1 := by
      rw [← _root_.pow_add, ← _root_.two_mul, _root_.pow_mul]; simp
    rw [Nat.add_sub_cancel, _root_.pow_succ]
    linear_combination (-X.det) * a
  have key : X * (adjugate X - ((-1) ^ (m - 1) : MvPolynomial (Fin m × Fin m) ℤ) • Sp X) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, e1, e2, hc, _root_.smul_neg, _root_.smul_smul, _root_.sub_neg_eq_add, ← _root_.add_smul, hs,
      _root_.zero_smul]
  have k2 : X.det • (adjugate X - ((-1) ^ (m - 1) : MvPolynomial (Fin m × Fin m) ℤ) • Sp X) = 0 := by
    have : X.det • (adjugate X - ((-1) ^ (m - 1) : MvPolynomial (Fin m × Fin m) ℤ) • Sp X) =
        (adjugate X * X) * (adjugate X - ((-1) ^ (m - 1) : MvPolynomial (Fin m × Fin m) ℤ) • Sp X) := by
      rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [this, Matrix.mul_assoc, key, Matrix.mul_zero]
  funext i j
  have := congrFun (congrFun k2 i) j
  simp only [Matrix.smul_apply, _root_.smul_eq_mul, Matrix.zero_apply, Matrix.sub_apply, _root_.mul_eq_zero] at this
  exact _root_.sub_eq_zero.mp (this.resolve_left hd)

theorem mapMatrix_smul {S : Type*} [CommRing S] (f : S →+* R) (c : S) (M : Matrix (Fin m) (Fin m) S) :
    f.mapMatrix (c • M) = f c • f.mapMatrix M := by
  ext i j; simp [RingHom.mapMatrix_apply]

theorem adj_poly (A : Matrix (Fin m) (Fin m) R) (hm : 1 ≤ m) :
    adjugate A = ((-1) ^ (m - 1) : R) • Sp A := by
  let f : MvPolynomial (Fin m × Fin m) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) fun p => A p.1 p.2
  have hA : f.mapMatrix (mvPolynomialX (Fin m) (Fin m) ℤ) = A := mvPolynomialX_map_eval₂ _ A
  have g := congrArg f.mapMatrix (adj_poly_generic hm)
  rw [RingHom.map_adjugate, hA, mapMatrix_smul, Sp, _root_.map_sum] at g
  rw [g, Sp]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mapMatrix_smul, _root_.map_pow, hA, ← Polynomial.coeff_map, ← Matrix.charpoly_map]
    congr 3

end Ring

/-! ## The iPRA theorem -/

variable {n m : ℕ} {Γ : List (Fm PTm n)}
open scoped Fm

/-- `(−1)^{m−1} ∑_{k<m} cf M (m − k − 1) · M^k`. -/
noncomputable def adjPolyZ (M : Mat m n) : Mat m n :=
  Mat.smul (ZT.signPow (m - 1) (ZT.natLit 1))
    (msumFin fun k : Fin m => Mat.smul (cfZ M (m - (k + 1))) (powM M k))

/-- `thm:adjpoly`: `adj M = (−1)^{m−1} ∑_{k<m} c_{k+1} M^k`. -/
theorem adjugate_polynomial (hm : 1 ≤ m) (M : Mat m n) : Γ ⊢[PRAAx] Mat.eqFm (Mat.adj M) (adjPolyZ M) := by
  refine Mat.derive ?_
  rw [Mat.toZ_adj, adj_poly _ hm, adjPolyZ, Mat.toZ_smul, ZT.toZ_signPow, ZT.toZ_natLit, toZ_msumFin, Sp,
    ← Fin.sum_univ_eq_sum_range (fun k => (Matrix.charpoly (Mat.toZ Γ M)).coeff (k + 1) • (Mat.toZ Γ M) ^ k)]
  simp only [Nat.cast_one, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Mat.toZ_smul, toZ_cfZ M (by omega), toZ_powM]
  congr 2
  have := k.isLt
  omega

end LeanProofs.IPRA.Algebra.AdjugatePolynomial
