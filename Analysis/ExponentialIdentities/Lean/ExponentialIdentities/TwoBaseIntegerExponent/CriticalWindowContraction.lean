import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The global terminal-prime contraction: kernel core

The critical-window report closes the entire factorial-cocycle feasibility target by a
global contraction: if a nonzero integer polynomial `P = ∑ c_j T^j` satisfies `P(M) = 0`,
then the `M`-weighted positive and negative coefficient masses balance exactly, while the
terminal-prime windows force every negative coefficient to be dominated by transported
positive-tail contributions whose `M`-weighted kernels are geometric.  Summing the window
inequalities against the mass balance yields `1 ≤ κ` for a contraction constant `κ < 1` in
the candidate regime (`M ≥ 2^14`, `q = M/A ≤ (2/3)^14`) — a contradiction that is uniform
in the degree, span, height, and sign pattern of `P`.

This module kernel-checks the complete finite skeleton:

* `mass_balance`, `sum_cpos_pos` — the sign-mass identity from `P(M) = 0`;
* `geom_mul_le_one`, `geom_pow_mul_le`, `weighted_geom_pow_mul_le` — the two summable
  kernels `∑ u^k` and `∑ ℓ M^{-ℓ}` in division-free form;
* `sum_Ioc_swap` — the exchange of the window and coefficient summations;
* `contraction_mul` — the abstract contraction: transport inequalities plus mass balance
  force `(1-u)(M-1)(M-2) ≤ ε(M-1)(M-2) + β(1-u)(M-2) + γ(1-u)(M-1)`;
* `kappa_mul_lt` — in the candidate regime the right side is strictly smaller;
* `no_balanced_transport` — hence no nonzero balanced coefficient vector satisfies the
  transport inequalities: the kernel core of the negative resolution of factorial
  feasibility;
* `exponent_gap_dvd` — the rational-root exponent-gap divisibility used by the report's
  Hermite-stencil diagnostics.

What remains outside the kernel is the arithmetic input that the transport inequalities do
hold for factorial cocycles at window primes: `V_p(t) = 1` and vanishing below the window
(kernel-checked in `TerminalFactorialIndependence`), the Legendre-interval upper bound at
higher levels, and Huxley's prime-window theorem (classical).
-/

namespace LeanProofs.TwoBaseIntegerExponent.CriticalWindow

open Finset

/-- Positive part of an integer coefficient, as a rational. -/
def cpos (c : ℕ → ℤ) (j : ℕ) : ℚ := max (c j : ℚ) 0

/-- Negative part of an integer coefficient, as a rational. -/
def cneg (c : ℕ → ℤ) (j : ℕ) : ℚ := max (-(c j : ℚ)) 0

lemma cpos_nonneg {c : ℕ → ℤ} {j : ℕ} : 0 ≤ cpos c j := le_max_right _ _

lemma cneg_nonneg {c : ℕ → ℤ} {j : ℕ} : 0 ≤ cneg c j := le_max_right _ _

lemma cpos_sub_cneg (c : ℕ → ℤ) (j : ℕ) : cpos c j - cneg c j = (c j : ℚ) := by
  unfold cpos cneg
  rcases le_total ((c j : ℚ)) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- **Sign-mass identity.**  If `∑ c_j M^j = 0`, the `M`-weighted positive and negative
masses agree. -/
theorem mass_balance {d : ℕ} {c : ℕ → ℤ} {M : ℚ}
    (hbal : ∑ j ∈ range (d + 1), (c j : ℚ) * M ^ j = 0) :
    ∑ j ∈ range (d + 1), cpos c j * M ^ j = ∑ j ∈ range (d + 1), cneg c j * M ^ j := by
  have h : ∑ j ∈ range (d + 1), cpos c j * M ^ j
      = ∑ j ∈ range (d + 1), (cneg c j * M ^ j + (c j : ℚ) * M ^ j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcj := cpos_sub_cneg c j
    linear_combination (M ^ j) * hcj
  rw [h, Finset.sum_add_distrib, hbal, add_zero]

/-- A nonzero balanced coefficient vector has strictly positive `M`-weighted positive
mass. -/
theorem sum_cpos_pos {d : ℕ} {c : ℕ → ℤ} {M : ℚ} (hM0 : 0 < M)
    (hne : ∃ j ∈ range (d + 1), c j ≠ 0)
    (hbal : ∑ j ∈ range (d + 1), (c j : ℚ) * M ^ j = 0) :
    0 < ∑ j ∈ range (d + 1), cpos c j * M ^ j := by
  obtain ⟨j0, hj0, hcj0⟩ := hne
  have hMj : 0 < M ^ j0 := pow_pos hM0 j0
  have hnn : ∀ x ∈ range (d + 1), 0 ≤ cpos c x * M ^ x :=
    fun x _ => mul_nonneg cpos_nonneg (pow_nonneg (le_of_lt hM0) x)
  have hnn' : ∀ x ∈ range (d + 1), 0 ≤ cneg c x * M ^ x :=
    fun x _ => mul_nonneg cneg_nonneg (pow_nonneg (le_of_lt hM0) x)
  rcases lt_trichotomy (c j0) 0 with h | h | h
  · have hc' : (c j0 : ℚ) < 0 := by exact_mod_cast h
    have hcneg : cneg c j0 = -(c j0 : ℚ) := max_eq_left (by linarith)
    calc (0:ℚ) < cneg c j0 * M ^ j0 := by rw [hcneg]; exact mul_pos (by linarith) hMj
      _ ≤ ∑ j ∈ range (d + 1), cneg c j * M ^ j := Finset.single_le_sum hnn' hj0
      _ = ∑ j ∈ range (d + 1), cpos c j * M ^ j := (mass_balance hbal).symm
  · exact absurd h hcj0
  · have hc' : (0:ℚ) < (c j0 : ℚ) := by exact_mod_cast h
    have hcpos : cpos c j0 = (c j0 : ℚ) := max_eq_left (le_of_lt hc')
    calc (0:ℚ) < cpos c j0 * M ^ j0 := by rw [hcpos]; exact mul_pos hc' hMj
      _ ≤ ∑ j ∈ range (d + 1), cpos c j * M ^ j := Finset.single_le_sum hnn hj0

/-! ### Division-free geometric kernels -/

/-- `(∑_{k<n} u^k)(1-u) = 1 - u^n ≤ 1` for `0 ≤ u`. -/
lemma geom_mul_le_one {u : ℚ} (hu0 : 0 ≤ u) (n : ℕ) :
    (∑ k ∈ range n, u ^ k) * (1 - u) ≤ 1 := by
  have h : (∑ k ∈ range n, u ^ k) * (1 - u) = 1 - u ^ n := by
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  rw [h]
  have := pow_nonneg hu0 n
  linarith

/-- `(∑_{k<j} M^k)(M-1) = M^j - 1 ≤ M^j`. -/
lemma geom_pow_mul_le (M : ℚ) (j : ℕ) :
    (∑ k ∈ range j, M ^ k) * (M - 1) ≤ M ^ j := by
  have h : (∑ k ∈ range j, M ^ k) * (M - 1) = M ^ j - 1 := by
    induction j with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  rw [h]; linarith

/-- The weighted kernel: `(∑_{k<j} (j-k) M^k)(M-2) ≤ M^j` for `M ≥ 3`. -/
lemma weighted_geom_pow_mul_le {M : ℚ} (hM : 3 ≤ M) (j : ℕ) :
    (∑ k ∈ range j, ((j - k : ℕ) : ℚ) * M ^ k) * (M - 2) ≤ M ^ j := by
  have hM0 : (0:ℚ) ≤ M := by linarith
  induction j with
  | zero => simp
  | succ m ih =>
    have split : ∑ k ∈ range (m + 1), ((m + 1 - k : ℕ) : ℚ) * M ^ k
        = ((∑ k ∈ range m, ((m - k : ℕ) : ℚ) * M ^ k)
            + ∑ k ∈ range m, M ^ k) + M ^ m := by
      rw [Finset.sum_range_succ]
      have h1 : (m + 1 - m : ℕ) = 1 := by omega
      rw [h1]
      push_cast
      rw [one_mul, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < m := Finset.mem_range.mp hk
      have h2 : (m + 1 - k : ℕ) = (m - k) + 1 := by omega
      rw [h2]
      push_cast
      ring
    rw [split, add_mul, add_mul]
    have hG := geom_pow_mul_le M m
    have hG0 : 0 ≤ ∑ k ∈ range m, M ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg hM0 k
    have hG2 : (∑ k ∈ range m, M ^ k) * (M - 2) ≤ M ^ m := by nlinarith [hG, hG0]
    have hMm : (0:ℚ) ≤ M ^ m := pow_nonneg hM0 m
    have hpow : M ^ m * (M - 2) = M ^ (m + 1) - 2 * M ^ m := by rw [pow_succ]; ring
    linarith [ih, hG2]

/-! ### The summation exchange -/

lemma Ioc_eq_filter (k d : ℕ) :
    Finset.Ioc k d = (range (d + 1)).filter (fun j => k < j) := by
  ext j
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
  omega

/-- Exchange the window index and the coefficient index. -/
lemma sum_Ioc_swap (f : ℕ → ℕ → ℚ) (d : ℕ) :
    ∑ k ∈ range (d + 1), ∑ j ∈ Finset.Ioc k d, f k j
      = ∑ j ∈ range (d + 1), ∑ k ∈ range j, f k j := by
  have h1 : ∀ k, ∑ j ∈ Finset.Ioc k d, f k j
      = ∑ j ∈ range (d + 1), if k < j then f k j else 0 := by
    intro k
    rw [Ioc_eq_filter, Finset.sum_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < d + 1 := Finset.mem_range.mp hj
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun k _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-! ### The abstract contraction -/

/-- **Abstract global terminal-prime contraction** (division-free form).  Suppose the
nonzero integer coefficients `c_0, …, c_d` are `M`-balanced (`∑ c_j M^j = 0`) and that
every negative coefficient obeys the terminal-window transport inequality
`(-c_k) ≤ ∑_{j>k} c_j⁺ (ε u^k M^{j-k} + β + γ (j-k))`.  Then the contraction constant is
at least one:
`(1-u)(M-1)(M-2) ≤ ε(M-1)(M-2) + β(1-u)(M-2) + γ(1-u)(M-1)`. -/
theorem contraction_mul {d : ℕ} {c : ℕ → ℤ} {M u ε β γ : ℚ}
    (hM : 3 ≤ M) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hε : 0 ≤ ε) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hne : ∃ j ∈ range (d + 1), c j ≠ 0)
    (hbal : ∑ j ∈ range (d + 1), (c j : ℚ) * M ^ j = 0)
    (htrans : ∀ k ∈ range (d + 1), c k < 0 →
      (-(c k : ℚ)) ≤ ∑ j ∈ Finset.Ioc k d,
        cpos c j * (ε * u ^ k * M ^ (j - k) + β + γ * ((j - k : ℕ) : ℚ))) :
    (1 - u) * (M - 1) * (M - 2) ≤
      ε * (M - 1) * (M - 2) + β * (1 - u) * (M - 2) + γ * (1 - u) * (M - 1) := by
  have hM0 : (0:ℚ) ≤ M := by linarith
  have h1u : (0:ℚ) < 1 - u := by linarith
  have hM1 : (0:ℚ) < M - 1 := by linarith
  have hM2 : (0:ℚ) < M - 2 := by linarith
  have hPi : (0:ℚ) < (1 - u) * (M - 1) * (M - 2) := mul_pos (mul_pos h1u hM1) hM2
  have hSpos : 0 < ∑ j ∈ range (d + 1), cpos c j * M ^ j :=
    sum_cpos_pos (by linarith) hne hbal
  -- Step 1: the per-window inequality, multiplied through by `M^k`.
  have step1 : ∀ k ∈ range (d + 1), cneg c k * M ^ k ≤
      ∑ j ∈ Finset.Ioc k d,
        (cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
          + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)) := by
    intro k hk
    by_cases hck : c k < 0
    · have hck' : (c k : ℚ) < 0 := by exact_mod_cast hck
      have hneg : cneg c k = -(c k : ℚ) := max_eq_left (by linarith)
      have hMk : (0:ℚ) ≤ M ^ k := pow_nonneg hM0 k
      have ht := mul_le_mul_of_nonneg_right (htrans k hk hck) hMk
      rw [Finset.sum_mul] at ht
      rw [hneg]
      refine ht.trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
      have hkj : k ≤ j := le_of_lt (Finset.mem_Ioc.mp hj).1
      have hpow : M ^ (j - k) * M ^ k = M ^ j := by
        rw [← pow_add]
        congr 1
        omega
      linear_combination (cpos c j * ε * u ^ k) * hpow
    · have hck' : (0:ℚ) ≤ (c k : ℚ) := by exact_mod_cast not_lt.mp hck
      have h0 : cneg c k = 0 := max_eq_right (by linarith)
      rw [h0, zero_mul]
      refine Finset.sum_nonneg fun j hj => ?_
      have hcp : (0:ℚ) ≤ cpos c j := cpos_nonneg
      have hMk : (0:ℚ) ≤ M ^ k := pow_nonneg hM0 k
      have hMj : (0:ℚ) ≤ M ^ j := pow_nonneg hM0 j
      have huk : (0:ℚ) ≤ u ^ k := pow_nonneg hu0 k
      have hl : (0:ℚ) ≤ ((j - k : ℕ) : ℚ) := Nat.cast_nonneg _
      have t1 : (0:ℚ) ≤ cpos c j * (ε * u ^ k * M ^ j) :=
        mul_nonneg hcp (mul_nonneg (mul_nonneg hε huk) hMj)
      have t2 : (0:ℚ) ≤ cpos c j * (β * M ^ k) :=
        mul_nonneg hcp (mul_nonneg hβ hMk)
      have t3 : (0:ℚ) ≤ cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k) :=
        mul_nonneg hcp (mul_nonneg (mul_nonneg hγ hl) hMk)
      linarith
  -- Step 2: sum over the windows and exchange the summations.
  have step2 : ∑ j ∈ range (d + 1), cneg c j * M ^ j ≤
      ∑ j ∈ range (d + 1), ∑ k ∈ range j,
        (cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
          + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)) := by
    calc ∑ j ∈ range (d + 1), cneg c j * M ^ j
        ≤ ∑ k ∈ range (d + 1), ∑ j ∈ Finset.Ioc k d,
            (cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
              + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)) :=
          Finset.sum_le_sum step1
      _ = _ := sum_Ioc_swap
          (fun k j => cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
            + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)) d
  -- Step 3: per-coefficient geometric bounds, multiplied by the positive constant.
  have inner_bound : ∀ j ∈ range (d + 1),
      (∑ k ∈ range j,
        (cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
          + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)))
        * ((1 - u) * (M - 1) * (M - 2))
      ≤ cpos c j * M ^ j *
          (ε * (M - 1) * (M - 2) + β * (1 - u) * (M - 2) + γ * (1 - u) * (M - 1)) := by
    intro j _
    have e1 : ∑ k ∈ range j, cpos c j * (ε * u ^ k * M ^ j)
        = (cpos c j * ε * M ^ j) * ∑ k ∈ range j, u ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k ∈ range j, cpos c j * (β * M ^ k)
        = (cpos c j * β) * ∑ k ∈ range j, M ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e3 : ∑ k ∈ range j, cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)
        = (cpos c j * γ) * ∑ k ∈ range j, ((j - k : ℕ) : ℚ) * M ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3]
    have hA := geom_mul_le_one hu0 j
    have hG := geom_pow_mul_le M j
    have hW := weighted_geom_pow_mul_le hM j
    have hA0 : 0 ≤ ∑ k ∈ range j, u ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg hu0 k
    have hG0 : 0 ≤ ∑ k ∈ range j, M ^ k :=
      Finset.sum_nonneg fun k _ => pow_nonneg hM0 k
    have hW0 : 0 ≤ ∑ k ∈ range j, ((j - k : ℕ) : ℚ) * M ^ k :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM0 k)
    have hcp : (0:ℚ) ≤ cpos c j := cpos_nonneg
    have hMj : (0:ℚ) ≤ M ^ j := pow_nonneg hM0 j
    have f1 : (0:ℚ) ≤ cpos c j * ε * M ^ j * ((M - 1) * (M - 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hcp hε) hMj)
        (le_of_lt (mul_pos hM1 hM2))
    have f2 : (0:ℚ) ≤ cpos c j * β * ((1 - u) * (M - 2)) :=
      mul_nonneg (mul_nonneg hcp hβ) (le_of_lt (mul_pos h1u hM2))
    have f3 : (0:ℚ) ≤ cpos c j * γ * ((1 - u) * (M - 1)) :=
      mul_nonneg (mul_nonneg hcp hγ) (le_of_lt (mul_pos h1u hM1))
    have b1 := mul_le_mul_of_nonneg_left hA f1
    have b2 := mul_le_mul_of_nonneg_left hG f2
    have b3 := mul_le_mul_of_nonneg_left hW f3
    nlinarith [b1, b2, b3]
  -- Combine.
  have hfinal : (∑ j ∈ range (d + 1), cneg c j * M ^ j)
        * ((1 - u) * (M - 1) * (M - 2))
      ≤ (∑ j ∈ range (d + 1), cpos c j * M ^ j) *
          (ε * (M - 1) * (M - 2) + β * (1 - u) * (M - 2) + γ * (1 - u) * (M - 1)) := by
    calc (∑ j ∈ range (d + 1), cneg c j * M ^ j) * ((1 - u) * (M - 1) * (M - 2))
        ≤ (∑ j ∈ range (d + 1), ∑ k ∈ range j,
            (cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
              + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)))
            * ((1 - u) * (M - 1) * (M - 2)) :=
          mul_le_mul_of_nonneg_right step2 (le_of_lt hPi)
      _ = ∑ j ∈ range (d + 1),
            (∑ k ∈ range j,
              (cpos c j * (ε * u ^ k * M ^ j) + cpos c j * (β * M ^ k)
                + cpos c j * (γ * ((j - k : ℕ) : ℚ) * M ^ k)))
              * ((1 - u) * (M - 1) * (M - 2)) := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ range (d + 1), cpos c j * M ^ j *
            (ε * (M - 1) * (M - 2) + β * (1 - u) * (M - 2) + γ * (1 - u) * (M - 1)) :=
          Finset.sum_le_sum inner_bound
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [← mass_balance hbal] at hfinal
  nlinarith [hfinal, hSpos]

/-! ### The candidate-regime numerics -/

/-- In the candidate regime (`M ≥ 2^14`, `0 ≤ q ≤ (2/3)^14`, `n ≥ 1`), the contraction
constant with `ε = 2q^n`, `β = γ = 2` is strictly below one (division-free form). -/
theorem kappa_mul_lt {q M : ℚ} (hq0 : 0 ≤ q) (hq : q ≤ (2/3 : ℚ) ^ 14)
    (hM : (2:ℚ) ^ 14 ≤ M) {n : ℕ} (hn : n ≠ 0) :
    2 * q ^ n * (M - 1) * (M - 2) + 2 * (1 - q) * (M - 2) + 2 * (1 - q) * (M - 1)
      < (1 - q) * (M - 1) * (M - 2) := by
  have hq' : q ≤ 16384 / 4782969 := by
    have h : ((2:ℚ)/3) ^ 14 = 16384 / 4782969 := by norm_num
    linarith [hq, h.le, h.ge]
  have hM' : (16384:ℚ) ≤ M := by
    have h : ((2:ℚ)) ^ 14 = 16384 := by norm_num
    linarith [hM, h.le, h.ge]
  have hq1 : q < 1 := by linarith
  have hqn : q ^ n ≤ q := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    clear hn
    induction m with
    | zero => simp
    | succ m ih =>
      calc q ^ (m + 2) = q ^ (m + 1) * q := pow_succ q (m + 1)
        _ ≤ q * q := mul_le_mul_of_nonneg_right ih hq0
        _ ≤ 1 * q := mul_le_mul_of_nonneg_right (le_of_lt hq1) hq0
        _ = q := one_mul q
  have hqn0 : 0 ≤ q ^ n := pow_nonneg hq0 n
  have hM1 : (0:ℚ) < M - 1 := by linarith
  have hM2 : (0:ℚ) < M - 2 := by linarith
  have hP0 : (0:ℚ) < (M - 1) * (M - 2) := mul_pos hM1 hM2
  -- bounds on the product atoms
  have hPn : q ^ n * ((M - 1) * (M - 2)) ≤ (16384 / 4782969) * ((M - 1) * (M - 2)) :=
    mul_le_mul_of_nonneg_right (le_trans hqn hq') (le_of_lt hP0)
  have hqP : q * ((M - 1) * (M - 2)) ≤ (16384 / 4782969) * ((M - 1) * (M - 2)) :=
    mul_le_mul_of_nonneg_right hq' (le_of_lt hP0)
  have hPM : 16382 * (M - 1) ≤ (M - 1) * (M - 2) := by
    nlinarith [mul_nonneg (show (0:ℚ) ≤ M - 1 by linarith)
      (show (0:ℚ) ≤ M - 16384 by linarith)]
  have e2 : 2 * (1 - q) * (M - 2) ≤ 2 * (M - 2) := by
    nlinarith [mul_nonneg hq0 (le_of_lt hM2)]
  have e3 : 2 * (1 - q) * (M - 1) ≤ 2 * (M - 1) := by
    nlinarith [mul_nonneg hq0 (le_of_lt hM1)]
  nlinarith [hPn, hqP, hPM, e2, e3, hM']

/-- **Kernel core of the negative resolution of factorial feasibility.**  In the candidate
regime, no nonzero integer coefficient vector is `M`-balanced and satisfies the
terminal-window transport inequalities with the Legendre constants `ε = 2q^n`,
`β = γ = 2`. -/
theorem no_balanced_transport {q M : ℚ} (hq0 : 0 ≤ q) (hq : q ≤ (2/3 : ℚ) ^ 14)
    (hM : (2:ℚ) ^ 14 ≤ M) {n : ℕ} (hn : n ≠ 0) {d : ℕ} {c : ℕ → ℤ}
    (hne : ∃ j ∈ range (d + 1), c j ≠ 0)
    (hbal : ∑ j ∈ range (d + 1), (c j : ℚ) * M ^ j = 0)
    (htrans : ∀ k ∈ range (d + 1), c k < 0 →
      (-(c k : ℚ)) ≤ ∑ j ∈ Finset.Ioc k d,
        cpos c j * (2 * q ^ n * q ^ k * M ^ (j - k) + 2 + 2 * ((j - k : ℕ) : ℚ))) :
    False := by
  have hM3 : (3:ℚ) ≤ M := by
    have h : ((2:ℚ)) ^ 14 = 16384 := by norm_num
    linarith [hM, h.le, h.ge]
  have hq1 : q < 1 := by
    have h : ((2:ℚ)/3) ^ 14 = 16384 / 4782969 := by norm_num
    linarith [hq, h.le, h.ge]
  have hqn0 : (0:ℚ) ≤ 2 * q ^ n := by positivity
  have hcontr := contraction_mul (ε := 2 * q ^ n) (β := 2) (γ := 2)
    hM3 hq0 hq1 hqn0 (by norm_num) (by norm_num) hne hbal htrans
  have hκ := kappa_mul_lt hq0 hq hM hn
  linarith

/-! ### The rational-root exponent-gap lemma -/

/-- **Exponent-gap divisibility.**  If `a u^N + ∑_{j ≤ b} c_j u^j v^{N-j} = 0` with
`gcd(u,v) = 1` and `b < N`, then `v^{N-b} ∣ a`: a rational root `u/v` of a polynomial with
a gap of length `N - b` below its leading term forces the denominator power into the
leading coefficient. -/
theorem exponent_gap_dvd {a u v : ℤ} {N b : ℕ} (c : ℕ → ℤ) (hb : b < N)
    (huv : IsCoprime u v)
    (h : a * u ^ N + ∑ j ∈ range (b + 1), c j * u ^ j * v ^ (N - j) = 0) :
    v ^ (N - b) ∣ a := by
  have hdvd : v ^ (N - b) ∣ ∑ j ∈ range (b + 1), c j * u ^ j * v ^ (N - j) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j ≤ b := by
      have := Finset.mem_range.mp hj
      omega
    have hle : N - b ≤ N - j := by omega
    exact Dvd.dvd.mul_left (pow_dvd_pow v hle) _
  have h2 : v ^ (N - b) ∣ a * u ^ N := by
    have heq : a * u ^ N = -(∑ j ∈ range (b + 1), c j * u ^ j * v ^ (N - j)) := by
      linarith
    rw [heq]
    exact hdvd.neg_right
  exact (IsCoprime.pow huv.symm).dvd_of_dvd_mul_right h2

end LeanProofs.TwoBaseIntegerExponent.CriticalWindow
