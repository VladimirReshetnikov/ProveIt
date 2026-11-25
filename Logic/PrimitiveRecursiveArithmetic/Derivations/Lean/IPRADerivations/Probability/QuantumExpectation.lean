import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Parity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Quantum expectation values: realness and the variance identity

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/13_fourier_applications.tex`, Theorem
`thm:quantum`: "Let `ψ ∈ Q(i)^d` satisfy `ψ*ψ = 1`, and let `A ∈ Q(i)^{d×d}` be Hermitian. Put `⟨A⟩ = ψ*Aψ`. Then
`⟨A⟩` is real and `(ΔA)² := ψ*A²ψ − (ψ*Aψ)² = ‖(A − ⟨A⟩I)ψ‖² ≥ 0`."

Denominators are cleared, so the entries are integers, encoded as iPRA integer terms `ZT` (pairs of natural terms
read as differences, `Core/Integers`). The dimension `d` is a fixed metalevel number. Write `ψ = a + i b` and
`A = S + i T`; `A` is Hermitian when `S` is symmetric and `T` antisymmetric. With `Aψ = x + i y`
(`x_j = Σ_k (S_jk a_k − T_jk b_k)`, `y_j = Σ_k (S_jk b_k + T_jk a_k)`):

* `quantum_real`: `Im ψ*Aψ = Σ_j (a_j y_j − b_j x_j) = 0`, i.e. `⟨A⟩` is real;
* `quantum_square`: `Re ψ*A(Aψ) = ‖Aψ‖²`, i.e. `ψ*A²ψ = ‖Aψ‖²` (Hermiticity moves one `A` across);
* `quantum_variance`: with `N = ψ*ψ = Σ_j (a_j² + b_j²)` and `λ = Re ψ*Aψ = Σ_j (a_j x_j + b_j y_j)`,
  `Σ_j ((N x_j − λ a_j)² + (N y_j − λ b_j)²) = N (N ‖Aψ‖² − λ²)`, i.e. `‖(N A − λ)ψ‖² = N (N ψ*A²ψ − ⟨A⟩²)`. At
  `N = 1` this is the packet's `(ΔA)² = ‖(A − ⟨A⟩)ψ‖²`, and it is cleared of the normalization otherwise.

Each identity is a commutative-ring identity over finite sums (`*_alg`), transported to an iPRA derivation by
`ZT.derive`; realness divides by `2` through `two_cancel`. The sign follows from the identity with the integer-order
certificates of `Core/IntCertificates` (`nn_sum`, `nn_zsq`, `zle_of_comb`):

* `quantum_variance_nonneg`: `N (N ‖Aψ‖² − ⟨A⟩²) ≥ 0`, a sum of squares;
* `quantum_uncertainty`: for a normalized state (`ψ*ψ = 1`), `⟨A⟩² ≤ ψ*A²ψ`, i.e. `(ΔA)² ≥ 0`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.QuantumExpectation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Finite sums of integer terms -/

/-- The integer zero. -/
def zz : ZT n := ⟨zero, zero⟩

theorem toZ_zz : ZT.toZ Γ (zz : ZT n) = 0 := by simp [ZT.toZ, zz]

/-- `Σ_{i<d} f_i` for integer terms. -/
def zsum : {d : ℕ} → (Fin d → ZT n) → ZT n
  | 0, _ => zz
  | _ + 1, f => f 0 + zsum fun i => f i.succ

theorem toZ_zsum : {d : ℕ} → (f : Fin d → ZT n) → ZT.toZ Γ (zsum f) = ∑ i, ZT.toZ Γ (f i)
  | 0, _ => by simp [zsum, toZ_zz]
  | _ + 1, f => by rw [zsum, ZT.toZ_add, toZ_zsum, Fin.sum_univ_succ]

/-- `2 p = 2 q` gives `p = q`. -/
theorem two_cancel {p q : PTm n} (h : Γ ⊢[PRAAx] two * p ≐ two * q) : Γ ⊢[PRAAx] p ≐ q :=
  le_antisymm (mul_le_cancel (le_congr (.eqRefl _) h (le_refl _)))
    (mul_le_cancel (le_congr (.eqRefl _) h.eqSymm (le_refl _)))

/-! ## The ring identities -/

section Alg

variable {R : Type*} [CommRing R] {d : ℕ}

theorem imag_alg (A B X Y : Fin d → R) (S T : Fin d → Fin d → R)
    (hS : ∀ j k, S j k = S k j) (hT : ∀ j k, T j k = -T k j)
    (hX : ∀ j, X j = ∑ k, (S j k * A k - T j k * B k)) (hY : ∀ j, Y j = ∑ k, (S j k * B k + T j k * A k)) :
    (∑ j, (A j * Y j - B j * X j)) + (∑ j, (A j * Y j - B j * X j)) = 0 := by
  have hf : ∑ j, (A j * Y j - B j * X j) =
      ∑ j, ∑ k, (A j * (S j k * B k + T j k * A k) - B j * (S j k * A k - T j k * B k)) :=
    Finset.sum_congr rfl fun j _ => by rw [hX j, hY j, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc (∑ j, (A j * Y j - B j * X j)) + (∑ j, (A j * Y j - B j * X j))
      = (∑ j, ∑ k, (A j * (S j k * B k + T j k * A k) - B j * (S j k * A k - T j k * B k))) +
          ∑ j, ∑ k, (A k * (S k j * B j + T k j * A j) - B k * (S k j * A j - T k j * B j)) := by
        rw [hf]; congr 1; exact Finset.sum_comm
    _ = 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hS k j, hT k j]; ring

theorem square_alg (A B X Y : Fin d → R) (S T : Fin d → Fin d → R)
    (hS : ∀ j k, S j k = S k j) (hT : ∀ j k, T j k = -T k j)
    (hX : ∀ j, X j = ∑ k, (S j k * A k - T j k * B k)) (hY : ∀ j, Y j = ∑ k, (S j k * B k + T j k * A k)) :
    ∑ j, (A j * ∑ k, (S j k * X k - T j k * Y k) + B j * ∑ k, (S j k * Y k + T j k * X k)) =
      ∑ k, (X k * X k + Y k * Y k) := by
  have e1 : ∀ k, X k * X k + Y k * Y k =
      ∑ j, (X k * (S k j * A j - T k j * B j) + Y k * (S k j * B j + T k j * A j)) := fun k => by
    calc X k * X k + Y k * Y k
        = X k * (∑ j, (S k j * A j - T k j * B j)) + Y k * (∑ j, (S k j * B j + T k j * A j)) := by
          rw [← hX k, ← hY k]
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hS k j, hT k j]; ring

theorem variance_alg (A B X Y : Fin d → R) (N L V : R)
    (hN : N = ∑ j, (A j * A j + B j * B j)) (hL : L = ∑ j, (A j * X j + B j * Y j))
    (hV : V = ∑ j, (X j * X j + Y j * Y j)) :
    ∑ j, ((N * X j - L * A j) ^ 2 + (N * Y j - L * B j) ^ 2) = N * (N * V - L * L) := by
  have e : ∀ j, (N * X j - L * A j) ^ 2 + (N * Y j - L * B j) ^ 2 =
      N ^ 2 * (X j * X j + Y j * Y j) - 2 * N * L * (A j * X j + B j * Y j) + L ^ 2 * (A j * A j + B j * B j) :=
    fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← hN, ← hL, ← hV]
  ring

end Alg

/-! ## The quantum statements -/

section Quantum

variable {d : ℕ} (a b : Fin d → ZT n) (S T : Fin d → Fin d → ZT n)

/-- `Re (Aψ)_j`. -/
def xv (j : Fin d) : ZT n := zsum fun k => S j k * a k - T j k * b k
/-- `Im (Aψ)_j`. -/
def yv (j : Fin d) : ZT n := zsum fun k => S j k * b k + T j k * a k
/-- `ψ*ψ`. -/
def nrm : ZT n := zsum fun j => a j * a j + b j * b j
/-- `Re ψ*Aψ`. -/
def lam : ZT n := zsum fun j => a j * xv a b S T j + b j * yv a b S T j
/-- `Im ψ*Aψ`. -/
def imv : ZT n := zsum fun j => a j * yv a b S T j - b j * xv a b S T j
/-- `‖Aψ‖²`. -/
def nsq : ZT n := zsum fun j => xv a b S T j * xv a b S T j + yv a b S T j * yv a b S T j
/-- `Re ψ*A(Aψ)`. -/
def sq2 : ZT n := zsum fun j =>
  a j * zsum (fun k => S j k * xv a b S T k - T j k * yv a b S T k) +
    b j * zsum (fun k => S j k * yv a b S T k + T j k * xv a b S T k)

variable {a b S T}

theorem hX_at (j : Fin d) :
    ZT.toZ Γ (xv a b S T j) = ∑ k, (ZT.toZ Γ (S j k) * ZT.toZ Γ (a k) - ZT.toZ Γ (T j k) * ZT.toZ Γ (b k)) := by
  simp only [xv, toZ_zsum, ZT.toZ_sub, ZT.toZ_mul]

theorem hY_at (j : Fin d) :
    ZT.toZ Γ (yv a b S T j) = ∑ k, (ZT.toZ Γ (S j k) * ZT.toZ Γ (b k) + ZT.toZ Γ (T j k) * ZT.toZ Γ (a k)) := by
  simp only [yv, toZ_zsum, ZT.toZ_add, ZT.toZ_mul]

/-- `⟨A⟩` is real: `Im ψ*Aψ = 0` for Hermitian `A`. -/
theorem quantum_real (hS : ∀ j k, Γ ⊢[PRAAx] ZT.eq (S j k) (S k j))
    (hT : ∀ j k, Γ ⊢[PRAAx] ZT.eq (T j k) (-T k j)) : Γ ⊢[PRAAx] ZT.eq (imv a b S T) zz := by
  have h2 : Γ ⊢[PRAAx] ZT.eq (imv a b S T + imv a b S T) zz := by
    apply ZT.derive
    simp only [imv, toZ_zsum, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, toZ_zz]
    exact imag_alg _ _ _ _ _ _ (fun j k => ZT.toZ_eq (hS j k))
      (fun j k => (ZT.toZ_eq (hT j k)).trans (ZT.toZ_neg _)) hX_at hY_at
  have h2' : Γ ⊢[PRAAx] (imv a b S T).pos + (imv a b S T).pos + zero ≐ zero + ((imv a b S T).neg + (imv a b S T).neg) :=
    h2
  have h3 : Γ ⊢[PRAAx] two * (imv a b S T).pos ≐ two * (imv a b S T).neg := by
    ipra_lc natEq h2'
  show Γ ⊢[PRAAx] (imv a b S T).pos + zero ≐ zero + (imv a b S T).neg
  ipra_lc natEq (two_cancel h3)

/-- `ψ*A²ψ = ‖Aψ‖²` (real parts) for Hermitian `A`. -/
theorem quantum_square (hS : ∀ j k, Γ ⊢[PRAAx] ZT.eq (S j k) (S k j))
    (hT : ∀ j k, Γ ⊢[PRAAx] ZT.eq (T j k) (-T k j)) : Γ ⊢[PRAAx] ZT.eq (sq2 a b S T) (nsq a b S T) := by
  apply ZT.derive
  simp only [sq2, nsq, toZ_zsum, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]
  exact square_alg _ _ _ _ _ _ (fun j k => ZT.toZ_eq (hS j k))
    (fun j k => (ZT.toZ_eq (hT j k)).trans (ZT.toZ_neg _)) hX_at hY_at

/-- The variance identity `‖(N A − λ)ψ‖² = N (N ‖Aψ‖² − λ²)`, `N = ψ*ψ`, `λ = ⟨A⟩`. -/
theorem quantum_variance :
    Γ ⊢[PRAAx] ZT.eq
      (zsum fun j => ZT.sq (nrm a b * xv a b S T j - lam a b S T * a j) +
        ZT.sq (nrm a b * yv a b S T j - lam a b S T * b j))
      (nrm a b * (nrm a b * nsq a b S T - lam a b S T * lam a b S T)) := by
  apply ZT.derive
  simp only [toZ_zsum, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq]
  exact variance_alg _ _ _ _ _ _ _ (by simp only [nrm, toZ_zsum, ZT.toZ_add, ZT.toZ_mul])
    (by simp only [lam, toZ_zsum, ZT.toZ_add, ZT.toZ_mul]) (by simp only [nsq, toZ_zsum, ZT.toZ_add, ZT.toZ_mul])

/-- The squared residuals `Σ_j (|N x_j − λ a_j|² + |N y_j − λ b_j|²)`. -/
abbrev res (Γ : List (Fm PTm n)) (a b : Fin d → ZT n) (S T : Fin d → Fin d → ZT n) : Groth (Q Γ) :=
  ∑ j, (ZT.toZ Γ (nrm a b * xv a b S T j - lam a b S T * a j) ^ 2 +
    ZT.toZ Γ (nrm a b * yv a b S T j - lam a b S T * b j) ^ 2)

theorem res_nn : Nonneg Γ (res Γ a b S T) :=
  nn_sum _ _ fun j _ => nn_add (nn_zsq _) (nn_zsq _)

/-- `N (N ‖Aψ‖² − ⟨A⟩²) ≥ 0`. -/
theorem quantum_variance_nonneg :
    Γ ⊢[PRAAx] zle zz (nrm a b * (nrm a b * nsq a b S T - lam a b S T * lam a b S T)) := by
  have hv := ZT.toZ_eq (quantum_variance (Γ := Γ) (a := a) (b := b) (S := S) (T := T))
  have h1 : ZT.toZ Γ (zsum fun j => ZT.sq (nrm a b * xv a b S T j - lam a b S T * a j) +
      ZT.sq (nrm a b * yv a b S T j - lam a b S T * b j)) = res Γ a b S T := by
    simp only [toZ_zsum, ZT.toZ_add, ZT.toZ_sq]
  refine zle_of_comb (res Γ a b S T) ?_ res_nn
  rw [toZ_zz, sub_zero, ← hv, h1]

/-- `(ΔA)² ≥ 0`: for `ψ*ψ = 1` and Hermitian `A`, `⟨A⟩² ≤ ψ*A²ψ`. -/
theorem quantum_uncertainty (hS : ∀ j k, Γ ⊢[PRAAx] ZT.eq (S j k) (S k j))
    (hT : ∀ j k, Γ ⊢[PRAAx] ZT.eq (T j k) (-T k j)) (hN : Γ ⊢[PRAAx] ZT.eq (nrm a b) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (lam a b S T * lam a b S T) (sq2 a b S T) := by
  have hv := ZT.toZ_eq (quantum_variance (Γ := Γ) (a := a) (b := b) (S := S) (T := T))
  have h1 : ZT.toZ Γ (zsum fun j => ZT.sq (nrm a b * xv a b S T j - lam a b S T * a j) +
      ZT.sq (nrm a b * yv a b S T j - lam a b S T * b j)) = res Γ a b S T := by
    simp only [toZ_zsum, ZT.toZ_add, ZT.toZ_sq]
  have h2 : ZT.toZ Γ (nrm a b * (nrm a b * nsq a b S T - lam a b S T * lam a b S T)) =
      ZT.toZ Γ (nrm a b) * (ZT.toZ Γ (nrm a b) * ZT.toZ Γ (nsq a b S T) -
        ZT.toZ Γ (lam a b S T) * ZT.toZ Γ (lam a b S T)) := by
    simp only [ZT.toZ_mul, ZT.toZ_sub]
  have hq := ZT.toZ_eq (quantum_square (Γ := Γ) (a := a) (b := b) hS hT)
  have hn := ZT.toZ_eq hN
  rw [ZT.toZ_natLit, Nat.cast_one] at hn
  have hr := h1.symm.trans (hv.trans h2)
  refine zle_of_comb (res Γ a b S T) ?_ res_nn
  rw [ZT.toZ_mul]
  linear_combination hq - hr +
    (-(ZT.toZ Γ (nrm a b) + 1) * ZT.toZ Γ (nsq a b S T) + ZT.toZ Γ (lam a b S T) * ZT.toZ Γ (lam a b S T)) * hn

end Quantum

end LeanProofs.IPRA.Probability.QuantumExpectation
