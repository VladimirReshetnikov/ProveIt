import IPRADerivations.Algebra.CayleyHamilton

/-!
# The adjugate identities and the explicit inverse

Packet: `cayley_hamilton_ipra`, `sections/core.tex`, Lemma `lem:adjugate` and Theorem `thm:inverse`, for
integer matrices of every fixed size `k` with arbitrary integer-term entries.

* `row_expand`, `col_expand` (`lem:adjugate`): cofactor expansion along any row `i` and any column `j`,
  `det M = ∑_l m_{il} adj(M)_{li} = ∑_l m_{lj} adj(M)_{jl}`;
* `mul_adj`, `adj_mul` (`lem:adjugate`): `M adj M = adj M · M = (det M) I`;
* `inverse_right`, `inverse_left` (`thm:inverse`): if `u det A = 1`, then `u adj A` is a two-sided
  inverse of `A`;
* `unit_of_inverse` (`thm:inverse`, converse): a supplied right inverse `V`, `A V = I`, gives the unit
  witness `det A · det V = 1`.

Multiplicativity of the determinant (`lem:detmul`) is `Algebra/CayleyHamilton.det_mul`.
-/

namespace LeanProofs.IPRA.Algebra.AdjugateInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Matrix
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Projection from a finite conjunction. -/
theorem conjFin_elim : ∀ {k : ℕ} {f : Fin k → Fm PTm n}, (Γ ⊢[PRAAx] conjFin f) → ∀ i, Γ ⊢[PRAAx] f i
  | 0, _, _, i => i.elim0
  | 1, f, h, i => by
    have : i = 0 := Subsingleton.elim _ _
    subst this; exact h
  | k + 2, f, h, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Prf.andE₁ h
    · exact conjFin_elim (f := fun j : Fin (k + 1) => f j.succ) (Prf.andE₂ h) j

/-- A derived matrix equation gives equal evaluations. -/
theorem toZ_of_eqFm {k : ℕ} {M N : Mat k n} (h : Γ ⊢[PRAAx] Mat.eqFm M N) : Mat.toZ Γ M = Mat.toZ Γ N := by
  ext i j
  exact ZT.toZ_eq (conjFin_elim (conjFin_elim h i) j)

variable {k : ℕ}

/-- Row expansion: `det M = ∑_l m_{il} adj(M)_{li}`. -/
theorem row_expand (M : Mat k n) (i : Fin k) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det M) (ZT.sumFin fun l => M i l * Mat.adj M l i) :=
  ZT.derive (by
    rw [Mat.toZ_det, ZT.toZ_sumFin, Matrix.det_eq_sum_mul_adjugate_row _ i]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ZT.toZ_mul, ← Mat.toZ_apply, ← Mat.toZ_apply, Mat.toZ_adj])

/-- Column expansion: `det M = ∑_l m_{lj} adj(M)_{jl}`. -/
theorem col_expand (M : Mat k n) (j : Fin k) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det M) (ZT.sumFin fun l => M l j * Mat.adj M j l) :=
  ZT.derive (by
    rw [Mat.toZ_det, ZT.toZ_sumFin, Matrix.det_eq_sum_mul_adjugate_col _ j]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ZT.toZ_mul, ← Mat.toZ_apply, ← Mat.toZ_apply, Mat.toZ_adj])

/-- `M · adj M = (det M) I`. -/
theorem mul_adj (M : Mat k n) : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul M (Mat.adj M)) (Mat.smul (Mat.det M) Mat.one) :=
  Mat.derive (by simp [Matrix.mul_adjugate])

/-- `adj M · M = (det M) I`. -/
theorem adj_mul (M : Mat k n) : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (Mat.adj M) M) (Mat.smul (Mat.det M) Mat.one) :=
  Mat.derive (by simp [Matrix.adjugate_mul])

/-- `thm:inverse`: `u det A = 1` makes `u adj A` a right inverse. -/
theorem inverse_right {A : Mat k n} {u : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (u * Mat.det A) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul A (Mat.smul u (Mat.adj A))) Mat.one := by
  have e := ZT.toZ_eq h
  rw [ZT.toZ_mul, Mat.toZ_det, ZT.toZ_natLit] at e
  refine Mat.derive ?_
  rw [Mat.toZ_mul, Mat.toZ_smul, Mat.toZ_adj, Mat.toZ_one, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, e]
  simp

/-- `thm:inverse`: `u det A = 1` makes `u adj A` a left inverse. -/
theorem inverse_left {A : Mat k n} {u : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (u * Mat.det A) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (Mat.smul u (Mat.adj A)) A) Mat.one := by
  have e := ZT.toZ_eq h
  rw [ZT.toZ_mul, Mat.toZ_det, ZT.toZ_natLit] at e
  refine Mat.derive ?_
  rw [Mat.toZ_mul, Mat.toZ_smul, Mat.toZ_adj, Mat.toZ_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, e]
  simp

/-- `thm:inverse`, converse: a right inverse `V` gives `det A · det V = 1`. -/
theorem unit_of_inverse {A V : Mat k n} (h : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul A V) Mat.one) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det A * Mat.det V) (ZT.natLit 1) := by
  have e := toZ_of_eqFm h
  rw [Mat.toZ_mul, Mat.toZ_one] at e
  refine ZT.derive ?_
  rw [ZT.toZ_mul, Mat.toZ_det, Mat.toZ_det, ZT.toZ_natLit, ← Matrix.det_mul, e, Matrix.det_one]
  simp

end LeanProofs.IPRA.Algebra.AdjugateInverse
