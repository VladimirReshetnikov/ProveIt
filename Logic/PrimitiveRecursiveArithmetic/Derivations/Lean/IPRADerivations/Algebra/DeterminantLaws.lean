import IPRADerivations.Algebra.PrincipalMinors

/-!
# Laws of the determinant and similarity

Packet: `cayley_hamilton_ipra`, `sections/core.tex`:

* Lemma "Multilinearity, alternation, and transpose": "The determinant is additive and scalar-linear in
  each individual row or column. It vanishes when two rows, or two columns, are equal. Also
  `det(Mᵀ) = det M` and `det I_n = 1`";
* Corollary "Change of scalars and similarity": "If `P, Q` are supplied with `PQ = QP = I`, then
  `χ_{PAQ} = χ_A` and `f(PAQ) = P f(A) Q` for every scalar polynomial `f`".

For `k × k` integer matrices of every fixed size, with arbitrary integer-term entries
(`Core/LinearAlgebra`); `Mat.det` is the Laplace-expansion term.

* `updRow`, `updCol`: a matrix with one row or one column replaced by a vector of terms;
* `det_row_add`, `det_row_smul`, `det_col_add`, `det_col_smul`: additivity and scalar linearity in a
  row and in a column;
* `det_row_eq`, `det_col_eq`: two derivably equal rows (columns) give `det M = 0`;
* `det_transpose`, `det_one`;
* `det_conj`: `det(PAS) = det A` when `PS = SP = I` are derivable;
* `charpoly_conj`: the characteristic coefficients of `PAS` and `A` are equal (the explicit coefficient
  terms `cfZ` of `Algebra/CayleyHamiltonGeneral`);
* `pow_conj`: `(PAS)^j = P A^j S` for every `j`, including `j = 0`; a polynomial `f` is a finite sum of
  such terms.

Proposition "Finite generator form" (`sections/applications.tex`): "Suppose `φ(g_j) = ∑_{i<n} a_{ij} g_i`.
Writing `p = det(XI − A)`, one has `p(φ)(g_j) = 0` for every `j`":

* `chAt A Φ`: the characteristic polynomial of `A` evaluated at `Φ`; `generator_form`: `Φ G = G A`
  gives `χ_A(Φ) G = 0` (from `Φ^j G = G A^j` and `Algebra/CayleyHamiltonGeneral`), for square `G`.

Each statement is derived by evaluating both sides in the ring of the context and applying the
corresponding identity of commutative rings. The lemma on permutation signs concerns the permutation
expansion, which the Laplace term does not use.
-/

namespace LeanProofs.IPRA.Algebra.DeterminantLaws

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CayleyHamiltonGeneral
open LeanProofs.IPRA.Algebra.AdjugateInverse (toZ_of_eqFm)
open Matrix Polynomial
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-! ## Rows and columns -/

/-- `M` with the row `i` replaced by `v`. -/
def updRow (M : Mat k n) (i : Fin k) (v : Vec k n) : Mat k n := fun a b => if a = i then v b else M a b

/-- `M` with the column `j` replaced by `v`. -/
def updCol (M : Mat k n) (j : Fin k) (v : Vec k n) : Mat k n := fun a b => if b = j then v a else M a b

theorem toZ_updRow (M : Mat k n) (i : Fin k) (v : Vec k n) :
    Mat.toZ Γ (updRow M i v) = (Mat.toZ Γ M).updateRow i (Vec.toZ Γ v) := by
  ext a b
  by_cases h : a = i <;> simp [updRow, Matrix.updateRow_apply, Vec.toZ, h]

theorem toZ_updCol (M : Mat k n) (j : Fin k) (v : Vec k n) :
    Mat.toZ Γ (updCol M j v) = (Mat.toZ Γ M).updateCol j (Vec.toZ Γ v) := by
  ext a b
  by_cases h : b = j <;> simp [updCol, Matrix.updateCol_apply, Vec.toZ, h]

/-- The determinant is additive in each row. -/
theorem det_row_add (M : Mat k n) (i : Fin k) (u v : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (updRow M i (Vec.add u v)))
      (Mat.det (updRow M i u) + Mat.det (updRow M i v)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, Mat.toZ_det, toZ_updRow, Vec.toZ_add]
    exact Matrix.det_updateRow_add _ _ _ _)

/-- The determinant is scalar-linear in each row. -/
theorem det_row_smul (M : Mat k n) (i : Fin k) (c : ZT n) (u : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (updRow M i (Vec.smul c u))) (c * Mat.det (updRow M i u)) :=
  ZT.derive (by
    simp only [ZT.toZ_mul, Mat.toZ_det, toZ_updRow, Vec.toZ_smul]
    exact Matrix.det_updateRow_smul _ _ _ _)

/-- The determinant is additive in each column. -/
theorem det_col_add (M : Mat k n) (j : Fin k) (u v : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (updCol M j (Vec.add u v)))
      (Mat.det (updCol M j u) + Mat.det (updCol M j v)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, Mat.toZ_det, toZ_updCol, Vec.toZ_add]
    exact Matrix.det_updateCol_add _ _ _ _)

/-- The determinant is scalar-linear in each column. -/
theorem det_col_smul (M : Mat k n) (j : Fin k) (c : ZT n) (u : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (updCol M j (Vec.smul c u))) (c * Mat.det (updCol M j u)) :=
  ZT.derive (by
    simp only [ZT.toZ_mul, Mat.toZ_det, toZ_updCol, Vec.toZ_smul]
    exact Matrix.det_updateCol_smul _ _ _ _)

/-- Two equal rows: `det M = 0`. -/
theorem det_row_eq {M : Mat k n} {i j : Fin k} (hij : i ≠ j)
    (h : ∀ b, Γ ⊢[PRAAx] ZT.eq (M i b) (M j b)) : Γ ⊢[PRAAx] ZT.eq (Mat.det M) (ZT.natLit 0) :=
  ZT.derive (by
    rw [Mat.toZ_det, Matrix.det_zero_of_row_eq hij (funext fun b => ZT.toZ_eq (h b))]
    simp)

/-- Two equal columns: `det M = 0`. -/
theorem det_col_eq {M : Mat k n} {i j : Fin k} (hij : i ≠ j)
    (h : ∀ a, Γ ⊢[PRAAx] ZT.eq (M a i) (M a j)) : Γ ⊢[PRAAx] ZT.eq (Mat.det M) (ZT.natLit 0) :=
  ZT.derive (by
    rw [Mat.toZ_det, Matrix.det_zero_of_column_eq hij (fun a => ZT.toZ_eq (h a))]
    simp)

/-- `det(Mᵀ) = det M`. -/
theorem det_transpose (M : Mat k n) : Γ ⊢[PRAAx] ZT.eq (Mat.det (Mat.transpose M)) (Mat.det M) :=
  ZT.derive (by rw [Mat.toZ_det, Mat.toZ_det, Mat.toZ_transpose, Matrix.det_transpose])

/-- `det I = 1`. -/
theorem det_one : Γ ⊢[PRAAx] ZT.eq (Mat.det (Mat.one : Mat k n)) (ZT.natLit 1) :=
  ZT.derive (by rw [Mat.toZ_det, Mat.toZ_one, Matrix.det_one]; simp)

/-! ## Similarity -/

/-- `(P A S)^j = P A^j S` when `P S = S P = 1`. -/
theorem conj_pow {R : Type*} [CommRing R] {m : ℕ} (P S A : Matrix (Fin m) (Fin m) R)
    (h₁ : P * S = 1) (h₂ : S * P = 1) : ∀ j : ℕ, (P * A * S) ^ j = P * A ^ j * S
  | 0 => by simp [h₁]
  | j + 1 => by
    rw [_root_.pow_succ, conj_pow P S A h₁ h₂ j, _root_.pow_succ]
    calc P * A ^ j * S * (P * A * S) = P * A ^ j * (S * P) * A * S := by
          simp only [Matrix.mul_assoc]
      _ = P * (A ^ j * A) * S := by rw [h₂]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {P S A : Mat k n}

/-- `det(P A S) = det A` when `P S = S P = I`. -/
theorem det_conj (hPS : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul P S) Mat.one)
    (hSP : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul S P) Mat.one) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (Mat.mul (Mat.mul P A) S)) (Mat.det A) := by
  have h₁ := toZ_of_eqFm hPS
  have h₂ := toZ_of_eqFm hSP
  rw [Mat.toZ_mul, Mat.toZ_one] at h₁ h₂
  refine ZT.derive ?_
  rw [Mat.toZ_det, Mat.toZ_det, Mat.toZ_mul, Mat.toZ_mul, Matrix.det_mul, Matrix.det_mul]
  have d : (Mat.toZ Γ P).det * (Mat.toZ Γ S).det = 1 := by
    rw [← Matrix.det_mul, h₁, Matrix.det_one]
  linear_combination (Mat.toZ Γ A).det * d

/-- `χ_{PAS} = χ_A`: the characteristic coefficients agree. -/
theorem charpoly_conj (hPS : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul P S) Mat.one)
    (hSP : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul S P) Mat.one) {j : ℕ} (hj : j ≤ k) :
    Γ ⊢[PRAAx] ZT.eq (cfZ (Mat.mul (Mat.mul P A) S) j) (cfZ A j) := by
  have h₁ := toZ_of_eqFm hPS
  have h₂ := toZ_of_eqFm hSP
  rw [Mat.toZ_mul, Mat.toZ_one] at h₁ h₂
  refine ZT.derive ?_
  rw [toZ_cfZ _ hj, toZ_cfZ _ hj, Mat.toZ_mul, Mat.toZ_mul]
  have c := Matrix.charpoly_units_conj
    (⟨Mat.toZ Γ P, Mat.toZ Γ S, h₁, h₂⟩ : (Matrix (Fin k) (Fin k) (Groth (Q Γ)))ˣ) (Mat.toZ Γ A)
  rw [Matrix.inv_eq_right_inv h₁] at c
  exact congrArg (fun p => p.coeff (k - j)) c

/-- `(P A S)^j = P A^j S`. -/
theorem pow_conj (hPS : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul P S) Mat.one)
    (hSP : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul S P) Mat.one) (j : ℕ) :
    Γ ⊢[PRAAx] Mat.eqFm (powM (Mat.mul (Mat.mul P A) S) j) (Mat.mul (Mat.mul P (powM A j)) S) := by
  have h₁ := toZ_of_eqFm hPS
  have h₂ := toZ_of_eqFm hSP
  rw [Mat.toZ_mul, Mat.toZ_one] at h₁ h₂
  refine Mat.derive ?_
  rw [toZ_powM, Mat.toZ_mul, Mat.toZ_mul, Mat.toZ_mul, Mat.toZ_mul, toZ_powM]
  exact conj_pow _ _ _ h₁ h₂ j

/-! ## The finite generator form -/

/-- `Φ^j G = G A^j` when `Φ G = G A`. -/
theorem intertwine_pow {R : Type*} [CommRing R] {m : ℕ} (Φ G A : Matrix (Fin m) (Fin m) R)
    (h : Φ * G = G * A) : ∀ j : ℕ, Φ ^ j * G = G * A ^ j
  | 0 => by simp
  | j + 1 => by
    rw [_root_.pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, intertwine_pow Φ G A h j,
      Matrix.mul_assoc, ← _root_.pow_succ]

/-- `∑_{j ≤ k} cf A j · Φ^{k−j}`: the characteristic polynomial of `A` evaluated at `Φ`. -/
noncomputable def chAt (A Φ : Mat k n) : Mat k n :=
  msumFin fun j : Fin (k + 1) => Mat.smul (cfZ A j) (powM Φ (k - j))

/-- "Finite generator form": if `Φ G = G A` (the columns of `G` are generators `g_j` with
`φ(g_j) = ∑_i a_{ij} g_i`), then `χ_A(Φ) G = 0`, i.e. `χ_A(φ)(g_j) = 0` for every `j`. -/
theorem generator_form {A Φ G : Mat k n}
    (h : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul Φ G) (Mat.mul G A)) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (chAt A Φ) G) Mat.zero := by
  have h' := toZ_of_eqFm h
  rw [Mat.toZ_mul, Mat.toZ_mul] at h'
  have c := toZ_of_eqFm (cayley_hamilton (Γ := Γ) A)
  rw [Mat.toZ_zero, chZ, toZ_msumFin] at c
  refine Mat.derive ?_
  rw [Mat.toZ_mul, Mat.toZ_zero, chAt, toZ_msumFin, Finset.sum_mul]
  have e : ∀ j : Fin (k + 1),
      Mat.toZ Γ (Mat.smul (cfZ A j) (powM Φ (k - j))) * Mat.toZ Γ G =
        Mat.toZ Γ G * Mat.toZ Γ (Mat.smul (cfZ A j) (powM A (k - j))) := by
    intro j
    rw [Mat.toZ_smul, Mat.toZ_smul, toZ_powM, toZ_powM, Matrix.smul_mul, intertwine_pow _ _ _ h',
      Matrix.mul_smul]
  simp only [e]
  rw [← Finset.mul_sum, c, Matrix.mul_zero]

end LeanProofs.IPRA.Algebra.DeterminantLaws
