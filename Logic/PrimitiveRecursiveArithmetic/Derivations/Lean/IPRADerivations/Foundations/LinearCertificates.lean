import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Core.Order

/-!
# Certificates of the bounded linear solver and of the border action (`ipra_categorical_methods`, `lem:bounded-linear-solver`, `lem:action-finite-span`)

Packet: `foundations/ipra_categorical_methods`, `06_macaulay.tex`.

`lem:bounded-linear-solver`: "a fixed primitive recursive program returns either `c ∈ ℚⁿ` with
`Ac = v`, or `u ∈ ℚᵐ` with `uA = 0` and `uv ≠ 0`." The elimination carries a matrix `U` with
"The invariant is `[R | w] = U[A | v]`". Failure: "A putative solution `c` would give
`uv = uAc = 0`, so this is a genuine incompatibility certificate". Success: "The reduced pivot
pattern then gives `Rc = w`. Since row swaps, nonzero row rescalings, and row additions are
invertible, their inverse operations show `Ac = v`. One may track a second matrix for the
inverse operations; both products being identity are finite matrix equalities."

`lem:action-finite-span`: maintain "`m − ∑_j c_j b_j = ∑_ℓ h_ℓ f_ℓ`. On appending `X_k`, put
`c'_i = ∑_j (M_k)_{ij} c_j`, `h'_ℓ = X_k h_ℓ + ∑_j c_j h_{kjℓ}`. Multiply the previous identity
by `X_k` and substitute (border-action). The result is exactly the maintained identity with
`m' = X_k m`, `c'`, and `h'`."

For integer terms and matrices of arbitrary sizes (the sizes are parameters of the
metatheory; entries, vectors and the ring elements `b_j`, `f_ℓ`, `x`, `m` are arbitrary terms):

* `incompatible`: `uA = 0` and `Ac = v` give `u · v = 0`; `incompatible_cert`: with `u · v ≠ 0`
  the system has no solution;
* `solution_transport`: from `R = UA`, `w = Uv`, `WU = I` and `Rc = w`: `Ac = v`;
* `border_step`: from the maintained identity and the border action identities
  `x b_j − ∑_i M_{ij} b_i = ∑_ℓ H_{jℓ} f_ℓ`, the maintained identity for `x m`, `c' = Mc`,
  `h'_ℓ = x h_ℓ + ∑_j c_j H_{jℓ}`.

Each is a matrix identity over a commutative ring read in the ring of differences. Not derived:
the elimination program itself (pivot scan, the invariant along the loop, rational
normalization) and the reduction of a general polynomial.
-/

namespace LeanProofs.IPRA.Foundations.LinearCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

/-! ## The identities over a commutative ring -/

section Ring

variable {R : Type} [CommRing R] {m n : ℕ}

theorem incompatible_ring (A : Fin m → Fin n → R) (u v : Fin m → R) (c : Fin n → R)
    (hu : ∀ j, ∑ i, u i * A i j = 0) (hc : ∀ i, ∑ j, A i j * c j = v i) :
    ∑ i, u i * v i = 0 := by
  calc ∑ i, u i * v i = ∑ i, u i * ∑ j, A i j * c j := by simp [hc]
    _ = ∑ i, ∑ j, u i * A i j * c j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, ∑ i, u i * A i j * c j := Finset.sum_comm
    _ = ∑ j, (∑ i, u i * A i j) * c j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
    _ = 0 := by simp [hu]

theorem transport_ring (A Rm : Fin m → Fin n → R) (U W : Fin m → Fin m → R)
    (v w : Fin m → R) (c : Fin n → R)
    (hR : ∀ i j, Rm i j = ∑ l, U i l * A l j) (hw : ∀ i, w i = ∑ l, U i l * v l)
    (hWU : ∀ i l, ∑ t, W i t * U t l = if i = l then 1 else 0)
    (hc : ∀ i, ∑ j, Rm i j * c j = w i) (i : Fin m) : ∑ j, A i j * c j = v i := by
  have hR' : (Matrix.of Rm) = Matrix.of U * Matrix.of A := by
    ext i j; simp [Matrix.mul_apply, hR]
  have hWU' : Matrix.of W * Matrix.of U = 1 := by
    ext i l; simp [Matrix.mul_apply, Matrix.one_apply, hWU]
  have hc' : Matrix.mulVec (Matrix.of Rm) c = w := by
    funext i; simp [Matrix.mulVec, dotProduct, hc]
  have hw' : w = Matrix.mulVec (Matrix.of U) v := by
    funext i; simp [Matrix.mulVec, dotProduct, hw]
  have key : Matrix.mulVec (Matrix.of A) c = v := by
    calc Matrix.mulVec (Matrix.of A) c
        = Matrix.mulVec (Matrix.of W * Matrix.of U) (Matrix.mulVec (Matrix.of A) c) := by
          rw [hWU', Matrix.one_mulVec]
      _ = Matrix.mulVec (Matrix.of W) (Matrix.mulVec (Matrix.of Rm) c) := by
          rw [hR', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Matrix.mulVec (Matrix.of W * Matrix.of U) v := by
          rw [hc', hw', Matrix.mulVec_mulVec]
      _ = v := by rw [hWU', Matrix.one_mulVec]
  have := congrFun key i
  simpa [Matrix.mulVec, dotProduct] using this

theorem border_ring {N L : ℕ} (b c : Fin N → R) (f h : Fin L → R) (M : Fin N → Fin N → R)
    (H : Fin N → Fin L → R) (x mm : R)
    (hA : mm - ∑ j, c j * b j = ∑ l, h l * f l)
    (hB : ∀ j, x * b j - ∑ i, M i j * b i = ∑ l, H j l * f l) :
    x * mm - ∑ i, (∑ j, M i j * c j) * b i = ∑ l, (x * h l + ∑ j, c j * H j l) * f l := by
  have e1 : ∑ i, (∑ j, M i j * c j) * b i = ∑ j, c j * ∑ i, M i j * b i := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ l, (x * h l + ∑ j, c j * H j l) * f l =
      x * ∑ l, h l * f l + ∑ j, c j * ∑ l, H j l * f l := by
    simp only [_root_.add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have e3 : ∑ j, c j * (x * b j - ∑ i, M i j * b i) = ∑ j, c j * ∑ l, H j l * f l :=
    Finset.sum_congr rfl fun j _ => by rw [hB j]
  have e4 : ∑ j, c j * (x * b j) = x * ∑ j, c j * b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, ← e3]
  simp only [_root_.mul_sub, Finset.sum_sub_distrib]
  linear_combination x * hA - e4

end Ring

/-! ## The iPRA statements -/

variable {k : ℕ} {Γ : List (Fm PTm k)} {m n : ℕ}

/-- `uA = 0` and `Ac = v` give `u · v = 0`. -/
theorem incompatible (A : Fin m → Fin n → ZT k) (u v : Fin m → ZT k) (c : Fin n → ZT k)
    (hu : ∀ j, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => u i * A i j) (ZT.natLit 0))
    (hc : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => A i j * c j) (v i)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => u i * v i) (ZT.natLit 0) := by
  refine ZT.derive ?_
  have hu' := fun j => ZT.toZ_eq (hu j)
  have hc' := fun i => ZT.toZ_eq (hc i)
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at hu' hc' ⊢
  exact incompatible_ring _ _ _ _ hu' hc'

/-- `lem:bounded-linear-solver`, failure evidence: with `uA = 0` and `u · v ≠ 0` the system
`Ac = v` has no solution. -/
theorem incompatible_cert (A : Fin m → Fin n → ZT k) (u v : Fin m → ZT k) (c : Fin n → ZT k)
    (hu : ∀ j, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => u i * A i j) (ZT.natLit 0))
    (hne : Γ ⊢[PRAAx] neg (ZT.eq (ZT.sumFin fun i => u i * v i) (ZT.natLit 0)))
    (hc : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => A i j * c j) (v i)) : Γ ⊢[PRAAx] Fm.bot :=
  .impE hne (incompatible A u v c hu hc)

/-- The identity matrix entry. -/
def delta (i l : Fin m) : ZT k := if i = l then ZT.natLit 1 else ZT.natLit 0

theorem toZ_delta (i l : Fin m) :
    ZT.toZ Γ (delta (k := k) i l) = if i = l then 1 else 0 := by
  unfold delta
  split <;> simp [ZT.toZ_natLit]

/-- `lem:bounded-linear-solver`, success: a solution of the reduced system `Rc = w`, with
`R = UA`, `w = Uv` and a left inverse `W` of `U`, solves `Ac = v`. -/
theorem solution_transport (A Rm : Fin m → Fin n → ZT k) (U W : Fin m → Fin m → ZT k)
    (v w : Fin m → ZT k) (c : Fin n → ZT k)
    (hR : ∀ i j, Γ ⊢[PRAAx] ZT.eq (Rm i j) (ZT.sumFin fun l => U i l * A l j))
    (hw : ∀ i, Γ ⊢[PRAAx] ZT.eq (w i) (ZT.sumFin fun l => U i l * v l))
    (hWU : ∀ i l, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun t => W i t * U t l) (delta i l))
    (hc : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => Rm i j * c j) (w i)) (i : Fin m) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => A i j * c j) (v i) := by
  refine ZT.derive ?_
  have hR' := fun i j => ZT.toZ_eq (hR i j)
  have hw' := fun i => ZT.toZ_eq (hw i)
  have hWU' := fun i l => ZT.toZ_eq (hWU i l)
  have hc' := fun i => ZT.toZ_eq (hc i)
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, toZ_delta] at hR' hw' hWU' hc' ⊢
  exact transport_ring _ _ _ _ _ _ _ hR' hw' hWU' hc' i

/-- `lem:action-finite-span`, one step: appending a variable `x` to the word. -/
theorem border_step {N L : ℕ} (b c : Fin N → ZT k) (f h : Fin L → ZT k)
    (M : Fin N → Fin N → ZT k) (H : Fin N → Fin L → ZT k) (x mm : ZT k)
    (hA : Γ ⊢[PRAAx] ZT.eq (mm - ZT.sumFin fun j => c j * b j) (ZT.sumFin fun l => h l * f l))
    (hB : ∀ j, Γ ⊢[PRAAx] ZT.eq (x * b j - ZT.sumFin fun i => M i j * b i)
      (ZT.sumFin fun l => H j l * f l)) :
    Γ ⊢[PRAAx] ZT.eq (x * mm - ZT.sumFin fun i => (ZT.sumFin fun j => M i j * c j) * b i)
      (ZT.sumFin fun l => (x * h l + ZT.sumFin fun j => c j * H j l) * f l) := by
  refine ZT.derive ?_
  have hA' := ZT.toZ_eq hA
  have hB' := fun j => ZT.toZ_eq (hB j)
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_add] at hA' hB' ⊢
  exact border_ring _ _ _ _ _ _ _ _ hA' hB'

end LeanProofs.IPRA.Foundations.LinearCertificates
