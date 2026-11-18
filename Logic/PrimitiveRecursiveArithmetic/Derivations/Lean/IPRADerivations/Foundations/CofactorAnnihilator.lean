import IPRADerivations.Foundations.NullVectorDeterminant

/-!
# The cofactor annihilator of a hyperplane (`ipra_coherent_methods_2026-11-15`, `cor:weighted-subspace`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, corollary `cor:weighted-subspace`, proof:
"Exact Gaussian elimination produces a nonzero rational row vector `λ` annihilating `V` ...
Define `G_λ(X, Y) = Σ_{b ∈ B_L} λ_b b(X, Y)` ... All the given points are zeros of `G_λ`. Apply
Theorem `thm:weighted-zero-count`."

For a subspace spanned by `k` vectors `w_1, …, w_k` of length `k + 1` the annihilator needs no
elimination and no pivot search: the cofactor vector (the generalized cross product)
`λ_j = (−1)^j det(W without column j)` is orthogonal to every `w_i`, because the Laplace
expansion of a determinant with a repeated row vanishes. Integer terms, every `k` (a parameter
of the Lean statements); the `w_i` are the rows `1, …, k` of a matrix `M` whose row `0` is
irrelevant:

* `row_adj_zero`, `row_adj_succ`, `span_ring`, `adjugate_updateRow`: the facts over a
  commutative ring, from `M adj(M) = det(M) · 1`;
* `cof M`: the cofactor vector `λ_j = (adj M)_{j0}`;
* `cof_orthogonal`: `w_i · λ = 0` for every `i`;
* `span_annihilated`: if `v = Σ_i c_i w_i`, then `v · λ = 0`: every vector of the subspace is
  annihilated;
* `withRow`, `eval_det`: for an arbitrary vector `v`, `v · λ = det [v; w_1; …; w_k]`. With `v`
  the evaluation vector `Φ_L(P)` of a point this is the value `G_λ(P)`;
* `cof_expand`: the case `v = ` row `0` of `M`.

So `G_λ(P) = det [Φ_L(P); w_1; …; w_k]` vanishes at every point whose evaluation vector lies in
the span, and `λ ≠ 0` exactly when some such determinant is nonzero (a witness of
independence). Not derived: a subspace of smaller dimension given by fewer vectors (it must
first be completed to a hyperplane), the nonvanishing of the norm of `G_λ`, and the count of
`thm:weighted-zero-count`.
-/

namespace LeanProofs.IPRA.Foundations.CofactorAnnihilator

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Laplace expansion along row `0`. -/
theorem row_adj_zero (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    M 0 ⬝ᵥ (fun j => M.adjugate j 0) = M.det := by
  have h := congrFun (congrFun (Matrix.mul_adjugate M) 0) 0
  simpa [Matrix.mul_apply, dotProduct] using h

/-- Expansion of a determinant with a repeated row: the other rows are orthogonal to the
cofactors of row `0`. -/
theorem row_adj_succ (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (i : Fin k) :
    M i.succ ⬝ᵥ (fun j => M.adjugate j 0) = 0 := by
  have h := congrFun (congrFun (Matrix.mul_adjugate M) i.succ) 0
  simpa [Matrix.mul_apply, dotProduct, Fin.succ_ne_zero] using h

/-- A combination of the rows `1, …, k` is orthogonal to the cofactor vector. -/
theorem span_ring (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin k → R)
    (v : Fin (k + 1) → R) (h : ∀ l, v l = ∑ i, c i * M i.succ l) :
    v ⬝ᵥ (fun j => M.adjugate j 0) = 0 := by
  have e : v ⬝ᵥ (fun j => M.adjugate j 0) =
      ∑ i, c i * (M i.succ ⬝ᵥ fun j => M.adjugate j 0) := by
    simp only [dotProduct, h, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  exact Finset.sum_eq_zero fun i _ => by
    rw [row_adj_succ]
    exact MulZeroClass.mul_zero _

/-- The cofactors of row `0` do not depend on row `0`. -/
theorem adjugate_updateRow (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (v : Fin (k + 1) → R)
    (j : Fin (k + 1)) : (M.updateRow 0 v).adjugate j 0 = M.adjugate j 0 := by
  simp [Matrix.adjugate_apply]

/-- `v · λ = det [v; w_1; …; w_k]`. -/
theorem eval_ring (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (v : Fin (k + 1) → R) :
    v ⬝ᵥ (fun j => M.adjugate j 0) = (M.updateRow 0 v).det := by
  have h := row_adj_zero (M.updateRow 0 v)
  simp only [adjugate_updateRow, Matrix.updateRow_self] at h
  exact h

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k : ℕ}

/-- The cofactor vector of the rows `1, …, k`: `λ_j = (adj M)_{j0}`. -/
def cof (M : Mat (k + 1) n) : Vec (k + 1) n := fun j => Mat.adj M j 0

/-- The matrix with row `0` replaced by `v`. -/
def withRow (M : Mat (k + 1) n) (v : Vec (k + 1) n) : Mat (k + 1) n :=
  Fin.cons v fun i => M i.succ

theorem toZ_cof (M : Mat (k + 1) n) :
    Vec.toZ Γ (cof M) = fun j => (Mat.toZ Γ M).adjugate j 0 := by
  funext j
  rw [← Mat.toZ_adj]
  rfl

theorem toZ_withRow (M : Mat (k + 1) n) (v : Vec (k + 1) n) :
    Mat.toZ Γ (withRow M v) = (Mat.toZ Γ M).updateRow 0 (Vec.toZ Γ v) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [withRow, Mat.toZ, Vec.toZ]
  · simp [withRow, Mat.toZ, Fin.succ_ne_zero]

/-- Laplace expansion along row `0`: `M_0 · λ = det M`. -/
theorem cof_expand (M : Mat (k + 1) n) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot (M 0) (cof M)) (Mat.det M) :=
  ZT.derive (by
    rw [Vec.toZ_dot, Mat.toZ_det, toZ_cof]
    exact row_adj_zero (Mat.toZ Γ M))

/-- `cor:weighted-subspace`: the cofactor vector annihilates every spanning vector. -/
theorem cof_orthogonal (M : Mat (k + 1) n) (i : Fin k) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot (M i.succ) (cof M)) (ZT.natLit 0) :=
  ZT.derive (by
    rw [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_zero, toZ_cof]
    exact row_adj_succ (Mat.toZ Γ M) i)

/-- Every vector of the span is annihilated. -/
theorem span_annihilated {M : Mat (k + 1) n} {c : Vec k n} {v : Vec (k + 1) n}
    (h : Γ ⊢[PRAAx] Vec.eqFm v (fun l => ZT.sumFin fun i => c i * M i.succ l)) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot v (cof M)) (ZT.natLit 0) := by
  have e := Vec.toZ_eq h
  refine ZT.derive ?_
  rw [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_zero, toZ_cof]
  refine span_ring (Mat.toZ Γ M) (Vec.toZ Γ c) _ fun l => ?_
  have el := congrFun e l
  simpa [Vec.toZ, Mat.toZ] using el

/-- The value of the section: `v · λ = det [v; w_1; …; w_k]`. -/
theorem eval_det (M : Mat (k + 1) n) (v : Vec (k + 1) n) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot v (cof M)) (Mat.det (withRow M v)) :=
  ZT.derive (by
    rw [Vec.toZ_dot, Mat.toZ_det, toZ_cof, toZ_withRow]
    exact eval_ring _ _)

end LeanProofs.IPRA.Foundations.CofactorAnnihilator
