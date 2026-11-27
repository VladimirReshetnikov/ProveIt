import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import IPRADerivations.Foundations.NullVectorDeterminant

/-!
# A common point gives an elimination root (`ipra_resources_and_elimination_2026-11-15`, `lem:elim-root`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section 5: "Put `N = d + e`.
Let `S(U)` be the `N`-by-`N` matrix whose rows are coefficient vectors, in columns
`V^0, …, V^{N−1}`, of `F_c, V F_c, …, V^{e−1} F_c, G_c, V G_c, …, V^{d−1} G_c`. Define the
elimination polynomial `R(U) = det S(U)` (E4). This is a Sylvester determinant", and lemma
`lem:elim-root`: "If `F(x, y) = G(x, y) = 0`, then `R(x + cy) = 0`. Proof: Write `u = x + cy`,
`v = y`. The column `w = (1, v, …, v^{N−1})ᵀ` satisfies `S(u) w = 0`: each row evaluates a
shifted copy of `F_c` or `G_c` at `v`. Multiply by the adjugate of `S(u)`. The finite adjugate
identity gives `R(u) w = 0`, and its first component is `R(u) = 0`."

Derived for all degrees `d`, `e` with `d + e > 0` (parameters of the Lean statements) and
arbitrary integer terms `f_0, …, f_d`, `g_0, …, g_e` (the values at `u` of the coefficients of
`F_c`, `G_c` in powers of `V`) and `v`:

* `poly`, `poly_coeff`, `poly_natDegree`, `poly_eval`, `rowR`, `rowR_coeff`, `row_sum`: over a
  commutative ring, the row of the shifted polynomial `V^r P` against `(1, v, …, v^{N−1})` is
  `v^r P(v)`;
* `sylvR`, `sylvester_root`: the Sylvester matrix kills that column when `P(v) = Q(v) = 0`,
  hence its determinant vanishes;
* `vpow`, `rowT`, `sylv`: the powers `v^k`, the rows and the Sylvester matrix as integer terms;
* `elim_root`: from derivations of `Σ_{i ≤ d} f_i v^i = 0` and `Σ_{j ≤ e} g_j v^j = 0`, a
  derivation of `det S = 0`: the value `R(u)` of the elimination polynomial is zero.

With `Foundations/RationalRootScan` (the packet's `lem:elim-rational-roots`) and
`Foundations/IntersectionEnumeration` this is the completeness half of `thm:elim-complete` for
a supplied pair of coefficient lists. Not derived: the shear and the bounded generic direction
(`lem:elim-shear`), the degree audit `deg R ≤ de` (`lem:elim-degree`), the fibre multiplicity
(`lem:elim-fibre`) and the Bezout bound (`thm:elim-bezout`).
-/

namespace LeanProofs.IPRA.Foundations.EliminationRoot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open Syn Matrix Polynomial
open scoped Fm

section Ring

variable {R : Type*} [CommRing R]

/-- The polynomial with coefficients `a_0, …, a_d`. -/
noncomputable def poly (d : ℕ) (a : ℕ → R) : R[X] :=
  ∑ i ∈ Finset.range (d + 1), C (a i) * X ^ i

theorem poly_coeff (d : ℕ) (a : ℕ → R) (j : ℕ) :
    (poly d a).coeff j = if j ≤ d then a j else 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem poly_natDegree (d : ℕ) (a : ℕ → R) : (poly d a).natDegree ≤ d :=
  natDegree_sum_le_of_forall_le _ _ fun _ hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem poly_eval (d : ℕ) (a : ℕ → R) (v : R) :
    (poly d a).eval v = ∑ i ∈ Finset.range (d + 1), a i * v ^ i := by
  simp [poly, eval_finsetSum]

/-- The entry in column `k` of the coefficient row of `V^r P`. -/
def rowR (d : ℕ) (a : ℕ → R) (r k : ℕ) : R := if r ≤ k ∧ k ≤ r + d then a (k - r) else 0

theorem rowR_coeff (d : ℕ) (a : ℕ → R) (r k : ℕ) :
    rowR d a r k = (X ^ r * poly d a).coeff k := by
  rw [coeff_X_pow_mul', poly_coeff, rowR]
  by_cases h : r ≤ k
  · have e : (k ≤ r + d) ↔ (k - r ≤ d) := by omega
    simp [h, e]
  · simp [h]

/-- A shifted row against the powers of `v`: `Σ_k (V^r P)_k v^k = v^r P(v)`, here `0`. -/
theorem row_sum (d : ℕ) (a : ℕ → R) (r N : ℕ) (v : R) (hN : r + d < N)
    (hP : ∑ i ∈ Finset.range (d + 1), a i * v ^ i = 0) :
    ∑ k ∈ Finset.range N, rowR d a r k * v ^ k = 0 := by
  have hdeg : (X ^ r * poly d a).natDegree < N :=
    lt_of_le_of_lt
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le r) (poly_natDegree d a))) hN
  have h := eval_eq_sum_range' hdeg v
  simp only [← rowR_coeff] at h
  rw [← h, eval_mul, poly_eval, hP, MulZeroClass.mul_zero]

/-- The Sylvester matrix of two coefficient lists: `e` shifted rows of the first, then `d`
shifted rows of the second. -/
def sylvR (d e : ℕ) (a b : ℕ → R) : Matrix (Fin (e + d)) (Fin (e + d)) R :=
  Matrix.of fun i k =>
    Fin.addCases (fun r : Fin e => rowR d a r k) (fun s : Fin d => rowR e b s k) i

/-- A common root makes the Sylvester determinant vanish. -/
theorem sylvester_root (d e : ℕ) (a b : ℕ → R) (v : R) (h0 : 0 < e + d)
    (hP : ∑ i ∈ Finset.range (d + 1), a i * v ^ i = 0)
    (hQ : ∑ j ∈ Finset.range (e + 1), b j * v ^ j = 0) : (sylvR d e a b).det = 0 := by
  have hw : sylvR d e a b *ᵥ (fun k : Fin (e + d) => v ^ (k : ℕ)) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Fin.addCases (fun r => ?_) (fun s => ?_) i
    · simp only [sylvR, Matrix.of_apply, Fin.addCases_left]
      rw [Fin.sum_univ_eq_sum_range (fun k => rowR d a r k * v ^ k) (e + d)]
      exact row_sum d a r (e + d) v (by have := r.isLt; omega) hP
    · simp only [sylvR, Matrix.of_apply, Fin.addCases_right]
      rw [Fin.sum_univ_eq_sum_range (fun k => rowR e b s k * v ^ k) (e + d)]
      exact row_sum e b s (e + d) v (by have := s.isLt; omega) hQ
  have h1 : ((sylvR d e a b).det • (1 : Matrix (Fin (e + d)) (Fin (e + d)) R)) *ᵥ
      (fun k : Fin (e + d) => v ^ (k : ℕ)) = 0 := by
    rw [← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  have h2 := congrFun h1 ⟨0, h0⟩
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  simpa using h2

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The power `v^k` as an integer term. -/
def vpow (v : ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 1
  | k + 1 => v * vpow v k

theorem toZ_vpow (v : ZT n) : ∀ k, ZT.toZ Γ (vpow v k) = ZT.toZ Γ v ^ k
  | 0 => by simp [vpow]
  | k + 1 => by rw [vpow, ZT.toZ_mul, toZ_vpow v k, pow_succ']

/-- The entry in column `k` of the coefficient row of `V^r F`. -/
def rowT (d : ℕ) (f : ℕ → ZT n) (r k : ℕ) : ZT n :=
  if r ≤ k ∧ k ≤ r + d then f (k - r) else ZT.natLit 0

theorem toZ_rowT (d : ℕ) (f : ℕ → ZT n) (r k : ℕ) :
    ZT.toZ Γ (rowT d f r k) = rowR d (fun i => ZT.toZ Γ (f i)) r k := by
  unfold rowT rowR
  split_ifs <;> simp

/-- (E4): the Sylvester matrix of the coefficient terms. -/
def sylv (d e : ℕ) (f g : ℕ → ZT n) : Mat (e + d) n := fun i k =>
  Fin.addCases (fun r : Fin e => rowT d f r k) (fun s : Fin d => rowT e g s k) i

theorem toZ_sylv (d e : ℕ) (f g : ℕ → ZT n) :
    Mat.toZ Γ (sylv d e f g) =
      sylvR d e (fun i => ZT.toZ Γ (f i)) (fun j => ZT.toZ Γ (g j)) := by
  ext i k
  refine Fin.addCases (fun r => ?_) (fun s => ?_) i
  · simp [sylv, sylvR, Mat.toZ, toZ_rowT]
  · simp [sylv, sylvR, Mat.toZ, toZ_rowT]

/-- `lem:elim-root`: a common zero `v` of the two specialized polynomials gives
`det S = 0`. -/
theorem elim_root {d e : ℕ} {f g : ℕ → ZT n} {v : ZT n} (h0 : 0 < e + d)
    (hF : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i : Fin (d + 1) => f i * vpow v i) (ZT.natLit 0))
    (hG : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j : Fin (e + 1) => g j * vpow v j) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (sylv d e f g)) (ZT.natLit 0) := by
  have eF := ZT.toZ_eq hF
  have eG := ZT.toZ_eq hG
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, toZ_vpow, ZT.toZ_natLit, Nat.cast_zero] at eF eG
  rw [Fin.sum_univ_eq_sum_range (fun i => ZT.toZ Γ (f i) * ZT.toZ Γ v ^ i) (d + 1)] at eF
  rw [Fin.sum_univ_eq_sum_range (fun j => ZT.toZ Γ (g j) * ZT.toZ Γ v ^ j) (e + 1)] at eG
  refine ZT.derive ?_
  rw [Mat.toZ_det, toZ_sylv, ZT.toZ_natLit, Nat.cast_zero]
  exact sylvester_root d e _ _ _ h0 eF eG

end LeanProofs.IPRA.Foundations.EliminationRoot

export_ipra Foundations.EliminationRoot (vpow)
