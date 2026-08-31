import FabiusFunction.WeightedScaleMultiplicity
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# General-base multiplicity counts and digit recovery

The paper's zero-divisor calculation assigns multiplicity
`1 + padicValNat b n` to the positive integer `n` in the base-`b` geometric
sinc product.  This file formalizes the finite arithmetic identity behind
that count; the analytic identification of the zeros is separate:

`(b - 1) * ∑_{n=1}^N (1 + ν_b(n)) + s_b(N) = b * N`,

where `s_b(N)` is the sum of the base-`b` digits of `N`.  No primality
hypothesis is used, so the result applies unchanged to composite bases.  Its
quotient form is

`∑_{n=1}^N (1 + ν_b(n)) = (b * N - s_b(N)) / (b - 1)`.

The proof has two conceptual steps.  First, the generic layer-cake theorem
from `WeightedScaleMultiplicity` truncates the divisibility layers at the
natural logarithmic height.  Second, Mathlib's general-base digit identity
evaluates the resulting floor sum.  The additive formulation avoids
truncated division and makes the theorem total at `N = 0`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- Any range extending strictly beyond `log_b N` contains every scale layer
occurring among `1, …, N`.  This is a finite Fubini identity in every additive
commutative monoid, and `b` need not be prime. -/
theorem sum_range_weightedScaleMultiplicity_of_log_lt
    {M : Type*} [AddCommMonoid M] (b N H : ℕ) (w : ℕ → M)
    (hb : 1 < b) (hlog : Nat.log b N < H) :
    ∑ m ∈ range N, weightedScaleMultiplicity b w (m + 1) =
      ∑ h ∈ range H, (N / b ^ h) • w h := by
  have hheight : ∀ m ∈ range N,
      padicValNat b (m + 1) < H := by
    intro m hm
    have hmN : m + 1 ≤ N := by
      simp only [mem_range] at hm
      omega
    exact (padicValNat_le_nat_log (p := b) (m + 1)).trans_lt
      ((Nat.log_mono_right hmN).trans_lt hlog)
  have hlayer := sum_inclusivePrefixSum_eq_sum_filter_card_nsmul
    (range N) (fun m ↦ padicValNat b (m + 1)) w H hheight
  simp only [weightedScaleMultiplicity] at hlayer ⊢
  rw [hlayer]
  apply Finset.sum_congr rfl
  intro h hh
  have hfilter :
      (range N).filter (fun m ↦ h ≤ padicValNat b (m + 1)) =
        (range N).filter (fun m ↦ b ^ h ∣ m + 1) := by
    apply Finset.filter_congr
    intro m hm
    exact (Nat.pow_dvd_iff_le_padicValNat hb.ne' (by omega : m + 1 ≠ 0)).symm
  rw [hfilter, Nat.card_multiples]

/-- The sharp logarithmic range `0, …, log_b N` already contains every scale
layer occurring among `1, …, N`.  This strengthens
`sum_range_weightedScaleMultiplicity`, whose deliberately elementary bound
uses `range N`. -/
theorem sum_range_weightedScaleMultiplicity_log
    {M : Type*} [AddCommMonoid M] (b N : ℕ) (w : ℕ → M) (hb : 1 < b) :
    ∑ m ∈ range N, weightedScaleMultiplicity b w (m + 1) =
      ∑ h ∈ range (Nat.log b N).succ, (N / b ^ h) • w h :=
  sum_range_weightedScaleMultiplicity_of_log_lt
    b N (Nat.log b N).succ w hb (Nat.lt_succ_self _)

/-- Splitting off the zeroth floor layer gives the exact tail occurring in
Mathlib's general-base digit-sum formula.  The apparent final extra term is
zero because `N < b ^ (log_b N + 1)`. -/
theorem sum_range_div_pow_log_eq_self_add_tail (b N : ℕ) (hb : 1 < b) :
    (∑ h ∈ range (Nat.log b N).succ, N / b ^ h) =
      N + ∑ i ∈ range (Nat.log b N).succ, N / b ^ i.succ := by
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos (Nat.log b N)),
    pow_zero, Nat.div_one, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.succ_sub_one]
  rw [Finset.sum_range_succ,
    Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self hb N), add_zero]
  simp only [Nat.succ_eq_add_one, Nat.add_comm]

/-- **General-base digit recovery from cumulative scale multiplicities.**

For every integer base `b > 1`, including composite bases,

`(b - 1) * ∑_{n=1}^N (1 + ν_b(n)) + s_b(N) = bN`.

At `b = 2` this is the familiar binary zero-count formula.  The additive
form is exact in `ℕ`, including `N = 0`, and avoids any divisibility premise
needed to express the count as a quotient by `b - 1`. -/
theorem sub_one_mul_sum_padicValNat_succ_add_digitSum
    (b N : ℕ) (hb : 1 < b) :
    (b - 1) * (∑ m ∈ range N, (padicValNat b (m + 1) + 1)) +
        (Nat.digits b N).sum = b * N := by
  have hscale :
      (∑ m ∈ range N, (padicValNat b (m + 1) + 1)) =
        ∑ m ∈ range N,
          weightedScaleMultiplicity b (fun _ ↦ (1 : ℕ)) (m + 1) := by
    simp only [weightedScaleMultiplicity_one_nat]
  rw [hscale,
    sum_range_weightedScaleMultiplicity_log b N (fun _ ↦ (1 : ℕ)) hb]
  simp only [Nat.nsmul_eq_mul, mul_one]
  rw [sum_range_div_pow_log_eq_self_add_tail b N hb, Nat.mul_add,
    Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]
  have hdigit : (Nat.digits b N).sum ≤ N := Nat.digit_sum_le b N
  calc
    (b - 1) * N + (N - (Nat.digits b N).sum) + (Nat.digits b N).sum =
        (b - 1) * N + N := by
          rw [add_assoc, Nat.sub_add_cancel hdigit]
    _ = ((b - 1) + 1) * N := by rw [add_mul, one_mul]
    _ = b * N := by rw [Nat.sub_add_cancel hb.le]

/-- **Quotient form of the general-base zero count.**  The cumulative
multiplicity is the base-`b` digit complement divided by `b - 1`:

`∑_{n=1}^N (1 + ν_b(n)) = (bN - s_b(N)) / (b - 1)`.

This is the exact finite arithmetic statement used after identifying the
multiplicity of the `n`-th zero of the base-`b` sinc product. -/
theorem sum_range_padicValNat_succ_eq_sub_digitSum_div
    (b N : ℕ) (hb : 1 < b) :
    (∑ m ∈ range N, (padicValNat b (m + 1) + 1)) =
      (b * N - (Nat.digits b N).sum) / (b - 1) := by
  have hmain := sub_one_mul_sum_padicValNat_succ_add_digitSum b N hb
  have hprod :
      (b - 1) * (∑ m ∈ range N, (padicValNat b (m + 1) + 1)) =
        b * N - (Nat.digits b N).sum := by
    omega
  rw [← hprod, Nat.mul_comm (b - 1), Nat.mul_div_left _ (by omega)]

end Fabius
