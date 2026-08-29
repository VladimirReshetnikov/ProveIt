import FabiusFunction.ThueMorsePrefix
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum

/-!
# The counting interpretations of the prefix kernel

The umbrella gap register's *Prefix-kernel interpretations* candidate
records two classical readings of the B-spline kernel
`iteratedPrefixKernel k n = (n + k - 1).choose (k - 1)` that had no
Lean counterparts: it counts the ordered `k`-tuples of naturals summing
to `n`, and it is the `k`-fold discrete convolution power of the
constant kernel.  This module proves both, in the finite-support model
the register asks to choose: the tuples form the finset
`Finset.Nat.antidiagonalTuple k n`, and the convolution is the finite
antidiagonal sum.

The engine is the first-coordinate decomposition
`card_antidiagonalTuple_succ`, consumed twice: with the hockey-stick
identity it yields the closed count
`card_antidiagonalTuple = (n + k).choose k`, and by direct induction it
identifies the convolution power with the tuple count.  The register's
kernel is then both at once.

* `antidiagonalTuple_succ_eq`, `card_antidiagonalTuple_succ` — the
  first-coordinate decomposition and its cardinality form.
* `card_antidiagonalTuple` — stars and bars for weak compositions:
  `(n + k).choose k` ordered `(k+1)`-tuples summing to `n`.
* `natConv`, `constKernelConvPow` — finite-support discrete convolution
  and the convolution powers of the constant kernel.
* `constKernelConvPow_eq_card` — the power counts the tuples.
* `iteratedPrefixKernel_eq_card_antidiagonalTuple`,
  `iteratedPrefixKernel_eq_constKernelConvPow` — the register's two
  interpretations of the kernel, for every `k ≥ 1`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **First-coordinate decomposition of the weak compositions**: an
ordered `(k+1)`-tuple summing to `n` is a head `j` together with a
`k`-tuple summing to `n - j`. -/
theorem antidiagonalTuple_succ_eq (k n : ℕ) :
    Finset.Nat.antidiagonalTuple (k + 1) n =
      (Finset.antidiagonal n).biUnion fun p =>
        (Finset.Nat.antidiagonalTuple k p.2).image (Fin.cons p.1) := by
  ext x
  simp only [Finset.Nat.mem_antidiagonalTuple, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_antidiagonal, Prod.exists]
  constructor
  · intro hx
    refine ⟨x 0, ∑ i : Fin k, x i.succ, by rw [← hx, Fin.sum_univ_succ],
      Fin.tail x, rfl, ?_⟩
    exact Fin.cons_self_tail x
  · rintro ⟨a, b, hab, y, hy, rfl⟩
    rw [Fin.sum_cons, hy, hab]

/-- The cardinality form of the decomposition: the common lemma behind
both counting interpretations. -/
theorem card_antidiagonalTuple_succ (k n : ℕ) :
    (Finset.Nat.antidiagonalTuple (k + 1) n).card =
      ∑ p ∈ Finset.antidiagonal n,
        (Finset.Nat.antidiagonalTuple k p.2).card := by
  rw [antidiagonalTuple_succ_eq, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun p _ =>
      Finset.card_image_of_injective _ (Fin.cons_right_injective _)
  · intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxp hxq
    rw [Finset.mem_image] at hxp hxq
    obtain ⟨y, _, rfl⟩ := hxp
    obtain ⟨z, _, hzx⟩ := hxq
    apply hpq
    have hhead : q.1 = p.1 := by
      have := congrArg (fun f : Fin (k + 1) → ℕ => f 0) hzx
      simpa using this
    have hp' := Finset.mem_antidiagonal.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_antidiagonal.mp (Finset.mem_coe.mp hq)
    have : p.2 = q.2 := by omega
    exact Prod.ext hhead.symm this

/-- **Stars and bars for weak compositions** (the register's counting
candidate, subtraction-free form): there are exactly `(n + k).choose k`
ordered `(k+1)`-tuples of naturals summing to `n`. -/
theorem card_antidiagonalTuple (k n : ℕ) :
    (Finset.Nat.antidiagonalTuple (k + 1) n).card = (n + k).choose k := by
  induction k generalizing n with
  | zero =>
      simp [Finset.Nat.antidiagonalTuple_one]
  | succ k ih =>
      rw [card_antidiagonalTuple_succ,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [ih]
      calc
        (∑ i ∈ range (n + 1), (n - i + k).choose k) =
            ∑ i ∈ range (n + 1), (i + k).choose k := by
          rw [← Finset.sum_range_reflect]
          exact Finset.sum_congr rfl fun i hi => by
            congr 1
            have := Finset.mem_range.mp hi
            omega
        _ = (n + k + 1).choose (k + 1) := Nat.sum_range_add_choose n k
        _ = (n + (k + 1)).choose (k + 1) := by
          rw [Nat.add_assoc]

/-- Discrete convolution of finitely supported `ℕ`-indexed sequences,
as the finite antidiagonal sum — the register's chosen finite-support
model. -/
def natConv (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.antidiagonal n, f p.1 * g p.2

/-- The `k`-fold convolution power of the constant kernel `1`, with the
empty power the convolution unit `δ₀`. -/
def constKernelConvPow : ℕ → ℕ → ℕ
  | 0 => fun n => if n = 0 then 1 else 0
  | k + 1 => natConv (fun _ => 1) (constKernelConvPow k)

/-- **The convolution power counts the weak compositions**: the `k`-fold
power of the constant kernel at `n` is the number of ordered `k`-tuples
summing to `n`. -/
theorem constKernelConvPow_eq_card (k n : ℕ) :
    constKernelConvPow k n = (Finset.Nat.antidiagonalTuple k n).card := by
  induction k generalizing n with
  | zero =>
      cases n with
      | zero => simp [constKernelConvPow, Finset.Nat.antidiagonalTuple_zero_zero]
      | succ n => simp [constKernelConvPow, Finset.Nat.antidiagonalTuple_zero_succ]
  | succ k ih =>
      rw [card_antidiagonalTuple_succ]
      show natConv (fun _ => 1) (constKernelConvPow k) n = _
      unfold natConv
      exact Finset.sum_congr rfl fun p _ => by rw [one_mul, ih]

/-- **The prefix kernel counts the weak compositions** (the register's
first interpretation): for `k ≥ 1`, `iteratedPrefixKernel k n` is the
number of ordered `k`-tuples of naturals summing to `n`. -/
theorem iteratedPrefixKernel_eq_card_antidiagonalTuple
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    iteratedPrefixKernel k n = (Finset.Nat.antidiagonalTuple k n).card := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [card_antidiagonalTuple, iteratedPrefixKernel]
  congr 1

/-- **The prefix kernel is the convolution power of the constant
kernel** (the register's second interpretation): for `k ≥ 1`,
`iteratedPrefixKernel k` is the `k`-fold discrete convolution power of
the constant kernel `1`. -/
theorem iteratedPrefixKernel_eq_constKernelConvPow
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    iteratedPrefixKernel k n = constKernelConvPow k n := by
  rw [iteratedPrefixKernel_eq_card_antidiagonalTuple hk,
    constKernelConvPow_eq_card]

end Fabius
