import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NoncommRing

/-!
# Finite Neumann series and the corrected contraction

Packet: `foundations/ipra_observable_analysis_2026-11-20`, `lean/ObservableAnalysis/Neumann.lean` (stated
there for an abstract ring in host Lean): the exact left and right residuals of the finite geometric sum,
"no convergence hypothesis is used", and the "exact finite correction formula" for a candidate contracting
homotopy `h` of a differential `D` with `D² = 0`: with the defect `Δ = 1 − Dh − hD` and the corrected
contraction `h_N = h(1 + Δ + ⋯ + Δ^{N−1})`, `D h_N + h_N D = 1 − Δ^N`. "A separate explicit norm bound on the
right-hand residual is all that is needed for an approximate contraction."

Here the ring is that of `k × k` matrices of integer terms (any fixed size `k`, any number `N` of terms), so
every identity is an iPRA derivation of entrywise equations, from the derived hypothesis `D D = 0` only:

* `geometric_left`, `geometric_right`: `(1 − M)(1 + M + ⋯ + M^{N−1}) = 1 − M^N` and the same on the right;
* `defect_commutes`: `D Δ = Δ D`;
* `corrected_residual`: `D h_N + h_N D = 1 − Δ^N`.
-/

namespace LeanProofs.IPRA.Foundations.NeumannCorrection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.AdjugateInverse (toZ_of_eqFm)
open Finset
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- `M^j`. -/
def mpow (M : Mat k n) : ℕ → Mat k n
  | 0 => Mat.one
  | j + 1 => Mat.mul (mpow M j) M

/-- `1 + M + ⋯ + M^{j−1}`. -/
def gsum (M : Mat k n) : ℕ → Mat k n
  | 0 => Mat.zero
  | j + 1 => Mat.add (gsum M j) (mpow M j)

/-- The defect `Δ = 1 − Dh − hD`. -/
def defect (D h : Mat k n) : Mat k n := Mat.sub (Mat.sub Mat.one (Mat.mul D h)) (Mat.mul h D)

/-- The corrected contraction `h_N = h(1 + Δ + ⋯ + Δ^{N−1})`. -/
def corrected (D h : Mat k n) (N : ℕ) : Mat k n := Mat.mul h (gsum (defect D h) N)

theorem toZ_mpow (M : Mat k n) (j : ℕ) : Mat.toZ Γ (mpow M j) = Mat.toZ Γ M ^ j := by
  induction j with
  | zero => simp [mpow]
  | succ j ih => simp [mpow, ih, pow_succ]

theorem toZ_gsum (M : Mat k n) (j : ℕ) :
    Mat.toZ Γ (gsum M j) = ∑ i ∈ range j, Mat.toZ Γ M ^ i := by
  induction j with
  | zero => simp [gsum]
  | succ j ih => simp [gsum, ih, toZ_mpow, sum_range_succ]

/-- `(1 − M)(1 + M + ⋯ + M^{N−1}) = 1 − M^N`. -/
theorem geometric_left (M : Mat k n) (N : ℕ) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (Mat.sub Mat.one M) (gsum M N)) (Mat.sub Mat.one (mpow M N)) := by
  apply Mat.derive
  simp only [Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_one, toZ_gsum, toZ_mpow]
  exact mul_neg_geom_sum _ _

/-- `(1 + M + ⋯ + M^{N−1})(1 − M) = 1 − M^N`. -/
theorem geometric_right (M : Mat k n) (N : ℕ) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul (gsum M N) (Mat.sub Mat.one M)) (Mat.sub Mat.one (mpow M N)) := by
  apply Mat.derive
  simp only [Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_one, toZ_gsum, toZ_mpow]
  exact geom_sum_mul_neg _ _

private theorem commute_core {R : Type*} [Ring R] {d e : R} (hD : d * d = 0) :
    d * (1 - d * e - e * d) = (1 - d * e - e * d) * d := by
  have h1 : d * (d * e) = 0 := by rw [← _root_.mul_assoc, hD]; simp
  have h2 : e * d * d = 0 := by rw [_root_.mul_assoc, hD]; simp
  simp only [_root_.mul_sub, _root_.sub_mul, _root_.mul_one]
  rw [h1, h2]
  noncomm_ring

private theorem residual_core {R : Type*} [Ring R] {d e : R} (hD : d * d = 0) (N : ℕ) :
    d * (e * ∑ i ∈ range N, (1 - d * e - e * d) ^ i) + e * (∑ i ∈ range N, (1 - d * e - e * d) ^ i) * d =
      1 - (1 - d * e - e * d) ^ N := by
  have hc : Commute d (1 - d * e - e * d) := commute_core hD
  have hS : d * (∑ i ∈ range N, (1 - d * e - e * d) ^ i) =
      (∑ i ∈ range N, (1 - d * e - e * d) ^ i) * d :=
    (Commute.sum_right _ _ _ fun i _ => hc.pow_right i).eq
  calc d * (e * ∑ i ∈ range N, (1 - d * e - e * d) ^ i) +
        e * (∑ i ∈ range N, (1 - d * e - e * d) ^ i) * d
      = (d * e + e * d) * ∑ i ∈ range N, (1 - d * e - e * d) ^ i := by
        rw [_root_.mul_assoc e _ d, ← hS, _root_.add_mul, _root_.mul_assoc d e, _root_.mul_assoc e d]
    _ = (1 - (1 - d * e - e * d)) * ∑ i ∈ range N, (1 - d * e - e * d) ^ i := by
        congr 1; abel
    _ = 1 - (1 - d * e - e * d) ^ N := mul_neg_geom_sum _ _

/-- `D Δ = Δ D` when `D D = 0`. -/
theorem defect_commutes {D h : Mat k n} (hD : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul D D) Mat.zero) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.mul D (defect D h)) (Mat.mul (defect D h) D) := by
  have hD' := toZ_of_eqFm hD
  simp only [Mat.toZ_mul, Mat.toZ_zero] at hD'
  apply Mat.derive
  simp only [defect, Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_one]
  exact commute_core hD'

/-- The exact finite correction formula: `D h_N + h_N D = 1 − Δ^N` when `D D = 0`. -/
theorem corrected_residual {D h : Mat k n} (hD : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul D D) Mat.zero) (N : ℕ) :
    Γ ⊢[PRAAx] Mat.eqFm (Mat.add (Mat.mul D (corrected D h N)) (Mat.mul (corrected D h N) D))
      (Mat.sub Mat.one (mpow (defect D h) N)) := by
  have hD' := toZ_of_eqFm hD
  simp only [Mat.toZ_mul, Mat.toZ_zero] at hD'
  apply Mat.derive
  simp only [corrected, defect, Mat.toZ_add, Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_one, toZ_gsum, toZ_mpow]
  exact residual_core hD' N

end LeanProofs.IPRA.Foundations.NeumannCorrection
