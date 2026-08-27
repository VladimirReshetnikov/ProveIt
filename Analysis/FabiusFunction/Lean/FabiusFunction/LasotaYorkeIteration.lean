import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Iterated Lasota–Yorke inequalities (Doeblin–Fortet)

The abstract iteration engine behind the RPF/quasi-compactness layer
of the audits (Document 7's architecture): from a **one-step**
Lasota–Yorke pair for an operator `T` and two functionals — a strong
seminorm `L` (e.g. the Lipschitz seminorm) and a weak one `N`
(e.g. the sup norm) —

`L (T φ) ≤ α·L φ + C·N φ`,   `N (T φ) ≤ β·N φ`,

the `n`-step inequalities follow by pure algebra:

`N (T^[n] φ) ≤ βⁿ·N φ`, and
`L (T^[n] φ) ≤ αⁿ·L φ + C·(∑_{j<n} αʲβ^{n-1-j})·N φ
             ≤ αⁿ·L φ + C/(β-α)·βⁿ·N φ`  (for `α < β`),

the classical Doeblin–Fortet / Ionescu-Tulcea–Marinescu form: the
strong seminorm contracts at rate `α` up to a weak-seminorm remainder
of size `O(βⁿ)` — the essential spectral radius of `T` on the strong
space is at most `α`, while the Perron data live above it.  For the
arithmetic transfer operator `𝓛₁` of `TransferOperatorStep`
(`α = √2/4`, `β = √2/2`, `C = π/2`) the remainder constant is
`C/(β-α) = π·√2`.

Everything is stated for bare functionals `L N : E → ℝ` on an
arbitrary type — no normed-space structure is needed.

* `lasota_yorke_weak_iterate` — the weak half `N(T^[n]φ) ≤ βⁿ·Nφ`.
* `lasota_yorke_iterate` — the exact geometric-sum form.
* `lasota_yorke_iterate_of_lt` — the Doeblin–Fortet closed form.
* `transfer_doeblin_fortet_constant` — `(π/2)/(√2/2 - √2/4) = π·√2`.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

variable {E : Type*} (T : E → E) (L N : E → ℝ)

/-- **Weak half of the iterated Lasota–Yorke estimate**: the one-step
bound `N(Tψ) ≤ β·Nψ` iterates to `N(T^[n]φ) ≤ βⁿ·Nφ`. -/
theorem lasota_yorke_weak_iterate {β : ℝ} (hβ : 0 ≤ β)
    (hN : ∀ ψ, N (T ψ) ≤ β * N ψ) (φ : E) (n : ℕ) :
    N (T^[n] φ) ≤ β ^ n * N φ := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc N (T^[n + 1] φ) = N (T (T^[n] φ)) := by
            rw [Function.iterate_succ_apply']
        _ ≤ β * N (T^[n] φ) := hN _
        _ ≤ β * (β ^ n * N φ) := mul_le_mul_of_nonneg_left ih hβ
        _ = β ^ (n + 1) * N φ := by ring

/-- **Iterated Lasota–Yorke inequality, exact geometric-sum form**:
the one-step pair `L(Tψ) ≤ α·Lψ + C·Nψ`, `N(Tψ) ≤ β·Nψ` iterates to

`L(T^[n]φ) ≤ αⁿ·Lφ + C·(∑_{j<n} αʲ β^{n-1-j})·Nφ`. -/
theorem lasota_yorke_iterate {α β C : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hC : 0 ≤ C)
    (hL : ∀ ψ, L (T ψ) ≤ α * L ψ + C * N ψ)
    (hN : ∀ ψ, N (T ψ) ≤ β * N ψ) (φ : E) (n : ℕ) :
    L (T^[n] φ) ≤ α ^ n * L φ +
      C * (∑ j ∈ range n, α ^ j * β ^ (n - 1 - j)) * N φ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : L (T^[n + 1] φ) ≤ α * L (T^[n] φ) + C * N (T^[n] φ) := by
        rw [Function.iterate_succ_apply']
        exact hL _
      have hNn : N (T^[n] φ) ≤ β ^ n * N φ :=
        lasota_yorke_weak_iterate T N hβ hN φ n
      have hcongr : ∑ j ∈ range n, α ^ (j + 1) * β ^ (n - (j + 1)) =
          ∑ j ∈ range n, α * (α ^ j * β ^ (n - 1 - j)) :=
        Finset.sum_congr rfl (fun j hj => by
          have hjn : j < n := Finset.mem_range.mp hj
          have he : n - (j + 1) = n - 1 - j := by omega
          rw [he]
          ring)
      have hsum : ∑ j ∈ range (n + 1), α ^ j * β ^ (n - j) =
          β ^ n + α * ∑ j ∈ range n, α ^ j * β ^ (n - 1 - j) := by
        rw [Finset.sum_range_succ', hcongr, ← Finset.mul_sum, pow_zero,
          one_mul, Nat.sub_zero]
        ring
      have hidx : ∀ j : ℕ, n + 1 - 1 - j = n - j := fun j => by omega
      simp only [hidx]
      calc L (T^[n + 1] φ)
          ≤ α * L (T^[n] φ) + C * N (T^[n] φ) := hstep
        _ ≤ α * (α ^ n * L φ +
              C * (∑ j ∈ range n, α ^ j * β ^ (n - 1 - j)) * N φ) +
            C * (β ^ n * N φ) :=
            add_le_add (mul_le_mul_of_nonneg_left ih hα)
              (mul_le_mul_of_nonneg_left hNn hC)
        _ = α ^ (n + 1) * L φ +
            C * (β ^ n + α * ∑ j ∈ range n, α ^ j * β ^ (n - 1 - j)) *
              N φ := by ring
        _ = α ^ (n + 1) * L φ +
            C * (∑ j ∈ range (n + 1), α ^ j * β ^ (n - j)) * N φ := by
            rw [hsum]

/-- **Doeblin–Fortet closed form**: for `α < β` the geometric sum is
dominated by `βⁿ/(β-α)` (telescoping: `(β-α)·∑ = βⁿ - αⁿ`), giving the
classical two-norm inequality

`L(T^[n]φ) ≤ αⁿ·Lφ + C/(β-α)·βⁿ·Nφ` —

essential contraction at rate `α`, remainder `O(βⁿ)`. -/
theorem lasota_yorke_iterate_of_lt {α β C : ℝ} (hα : 0 ≤ α)
    (hαβ : α < β) (hC : 0 ≤ C)
    (hL : ∀ ψ, L (T ψ) ≤ α * L ψ + C * N ψ)
    (hN : ∀ ψ, N (T ψ) ≤ β * N ψ) (φ : E) (hNφ : 0 ≤ N φ) (n : ℕ) :
    L (T^[n] φ) ≤ α ^ n * L φ + C / (β - α) * β ^ n * N φ := by
  have hβ : 0 ≤ β := hα.trans hαβ.le
  have hβα : 0 < β - α := sub_pos.mpr hαβ
  have hmain := lasota_yorke_iterate T L N hα hβ hC hL hN φ n
  have hgeom : (∑ j ∈ range n, α ^ j * β ^ (n - 1 - j)) * (α - β) =
      α ^ n - β ^ n := geom_sum₂_mul α β n
  have hSle : ∑ j ∈ range n, α ^ j * β ^ (n - 1 - j) ≤
      β ^ n / (β - α) := by
    rw [le_div_iff₀ hβα]
    have h2 : (∑ j ∈ range n, α ^ j * β ^ (n - 1 - j)) * (β - α) =
        β ^ n - α ^ n := by linear_combination -hgeom
    rw [h2]
    linarith [pow_nonneg hα n]
  calc L (T^[n] φ) ≤ α ^ n * L φ +
        C * (∑ j ∈ range n, α ^ j * β ^ (n - 1 - j)) * N φ := hmain
    _ ≤ α ^ n * L φ + C * (β ^ n / (β - α)) * N φ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSle hC) hNφ)
    _ = α ^ n * L φ + C / (β - α) * β ^ n * N φ := by ring

/-- The concrete Doeblin–Fortet constant of the arithmetic transfer
operator `𝓛₁` (`TransferOperatorStep`): with contraction `α = √2/4`,
weak rate `β = √2/2` and coupling `C = π/2`, the remainder constant is
`C/(β-α) = π·√2`; the iterated estimate reads
`Lip(𝓛₁ⁿφ) ≤ (√2/4)ⁿ·Lip(φ) + π√2·(√2/2)ⁿ·‖φ‖∞`. -/
theorem transfer_doeblin_fortet_constant :
    π / 2 / (Real.sqrt 2 / 2 - Real.sqrt 2 / 4) = π * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hX : Real.sqrt 2 / 2 - Real.sqrt 2 / 4 = Real.sqrt 2 / 4 := by
    ring
  have hpos : (0:ℝ) < Real.sqrt 2 / 4 := by
    have := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
    linarith
  rw [hX, div_eq_iff hpos.ne']
  linear_combination (-π / 4) * h2

end Fabius
