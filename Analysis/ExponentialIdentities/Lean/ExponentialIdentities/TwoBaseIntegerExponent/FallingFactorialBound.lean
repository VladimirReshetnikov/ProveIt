import ExponentialIdentities.TwoBaseIntegerExponent.HigherDifference
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Falling-factorial coefficients and the dyadic strip power bound

This module proves the two elementary analytic estimates that control a Newton divided
difference of a real power `x ↦ x ^ λ` on a dyadic strip `[N, 2N]`.  They are the
ingredients `eq:falling-bound` and `eq:power-strip-bound` of the further Alaoglu--Erdős
report, and together they give the divided-difference bound `eq:dd-final-bound`.

## Falling-factorial coefficient bound

The `i`-th derivative of `x ↦ x ^ λ` carries the coefficient
`(λ)_{\underline i} = ∏_{k < i} (λ - k)`, which the repository already introduces as
`fallingRpowCoeff` in `HigherDifference.lean`; `fallingReal` is a reducible alias matching
the report's notation.  The bound proved here is

```
  |(λ)_{\underline i}| / i ! ≤ 2 ^ (λ + i)      (λ ≥ 0, i : ℕ)
```

with `2 ^ (λ + i)` the real power `Real.rpow`.  The report's argument splits on
`0 ≤ λ ≤ 1` versus `λ ≥ 1` and uses `n = ⌈λ⌉`.  The formalization below avoids the split by
taking `m = ⌊λ⌋₊`, so that `m ≤ λ < m + 1` unconditionally.  Then

* `|λ - k| ≤ m + 1 + k` for every `k : ℕ`, because `0 ≤ λ < m + 1`;
* `∏_{k < i} (m + 1 + k) = i ! * (m + i).choose i`, a rising-factorial identity proved by
  induction from `Nat.add_one_mul_choose_eq`;
* `(m + i).choose i ≤ 2 ^ (m + i)` is `Nat.choose_le_two_pow` — the row-sum bound of the
  report — and `m ≤ λ` upgrades `2 ^ (m + i)` to `2 ^ (λ + i)`.

Since `m ≤ λ`, this is exactly the report's `n - 1 ≤ λ` step with `n = m + 1`.

## Dyadic strip power bound

For `1 ≤ N ≤ x ≤ 2N` and `λ ≥ 0` one has `x ^ (λ - i) ≤ 2 ^ λ * N ^ (λ - i)`: when the
exponent `λ - i` is nonnegative use `x ≤ 2N`, and when it is negative use `x ≥ N` together
with `1 ≤ 2 ^ λ`.

## Main results

* `abs_fallingRpowCoeff_div_factorial_le`
* `rpow_le_of_mem_strip`
* `abs_fallingRpowCoeff_div_factorial_mul_rpow_le`
-/

open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The report's falling factorial `(λ)_{\underline i} = ∏_{k < i} (λ - k)`.  This is a
reducible alias of `fallingRpowCoeff`, the same coefficient family used by the
forward-difference development in `HigherDifference.lean`. -/
noncomputable abbrev fallingReal (lam : ℝ) (i : ℕ) : ℝ := fallingRpowCoeff lam i

/-- The rising-factorial identity `∏_{k < i} (m + 1 + k) = i ! * (m + i).choose i` over `ℕ`. -/
private theorem prod_range_add_eq_factorial_mul_choose (m i : ℕ) :
    (∏ k ∈ Finset.range i, (m + 1 + k)) = i ! * (m + i).choose i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hsucc :
          (m + i + 1) * (m + i).choose i = (m + i + 1).choose (i + 1) * (i + 1) :=
        Nat.add_one_mul_choose_eq (m + i) i
      have hidx : m + (i + 1) = m + i + 1 := by omega
      have hshift : m + 1 + i = m + i + 1 := by omega
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, hidx, hshift]
      calc i ! * (m + i).choose i * (m + i + 1)
          = i ! * ((m + i + 1) * (m + i).choose i) := by ring
        _ = i ! * ((m + i + 1).choose (i + 1) * (i + 1)) := by rw [hsucc]
        _ = (i + 1) * i ! * (m + i + 1).choose (i + 1) := by ring

/-- **Falling-factorial coefficient bound.**  For a nonnegative real exponent `lam` and any
order `i`, the normalized falling factorial `|(lam)_{\underline i}| / i !` is at most
`2 ^ (lam + i)`, the exponent being a real power.

This is the report's `eq:falling-bound`.  The proof compares each factor `|lam - k|` with
`m + 1 + k` for `m = ⌊lam⌋₊`, identifies `∏_{k < i} (m + 1 + k)` with
`i ! * (m + i).choose i`, and bounds the binomial coefficient by the sum `2 ^ (m + i)` of
its Pascal row. -/
theorem abs_fallingRpowCoeff_div_factorial_le (lam : ℝ) (hlam : 0 ≤ lam) (i : ℕ) :
    |fallingRpowCoeff lam i| / (i ! : ℝ) ≤ (2 : ℝ) ^ (lam + (i : ℝ)) := by
  have hfac : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast i.factorial_pos
  obtain ⟨m, hmle, hlt⟩ : ∃ m : ℕ, (m : ℝ) ≤ lam ∧ lam < (m : ℝ) + 1 :=
    ⟨⌊lam⌋₊, Nat.floor_le hlam, Nat.lt_floor_add_one lam⟩
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- Step 1: factorwise comparison `|lam - k| ≤ m + 1 + k`.
  have hstep1 :
      |fallingRpowCoeff lam i| ≤ ∏ k ∈ Finset.range i, ((m : ℝ) + 1 + (k : ℝ)) := by
    rw [fallingRpowCoeff, Finset.abs_prod]
    refine Finset.prod_le_prod (fun k _ ↦ abs_nonneg _) (fun k _ ↦ ?_)
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- Step 2: the rising factorial is `i !` times a binomial coefficient.
  have hstep2 :
      (∏ k ∈ Finset.range i, ((m : ℝ) + 1 + (k : ℝ)))
        = (i ! : ℝ) * (((m + i).choose i : ℕ) : ℝ) := by
    have h : ((∏ k ∈ Finset.range i, (m + 1 + k) : ℕ) : ℝ)
        = ((i ! * (m + i).choose i : ℕ) : ℝ) := by
      rw [prod_range_add_eq_factorial_mul_choose]
    push_cast at h
    exact h
  -- Step 3: the Pascal row-sum bound, transported to the real exponent `lam`.
  have hchoose : (((m + i).choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (lam + (i : ℝ)) := by
    have h1 : (((m + i).choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + i) := by
      exact_mod_cast Nat.choose_le_two_pow (m + i) i
    have h2 : (2 : ℝ) ^ (m + i) = (2 : ℝ) ^ (((m + i : ℕ) : ℝ)) :=
      (Real.rpow_natCast (2 : ℝ) (m + i)).symm
    have h3 : ((m + i : ℕ) : ℝ) ≤ lam + (i : ℝ) := by
      push_cast
      linarith
    exact h1.trans
      (h2.trans_le (Real.rpow_le_rpow_of_exponent_le (by norm_num) h3))
  rw [div_le_iff₀' hfac]
  calc |fallingRpowCoeff lam i|
      ≤ ∏ k ∈ Finset.range i, ((m : ℝ) + 1 + (k : ℝ)) := hstep1
    _ = (i ! : ℝ) * (((m + i).choose i : ℕ) : ℝ) := hstep2
    _ ≤ (i ! : ℝ) * (2 : ℝ) ^ (lam + (i : ℝ)) :=
        mul_le_mul_of_nonneg_left hchoose hfac.le

/-- The falling-factorial coefficient bound, stated with the report's notation
`fallingReal`. -/
theorem abs_fallingReal_div_factorial_le (lam : ℝ) (hlam : 0 ≤ lam) (i : ℕ) :
    |fallingReal lam i| / (i ! : ℝ) ≤ (2 : ℝ) ^ (lam + (i : ℝ)) :=
  abs_fallingRpowCoeff_div_factorial_le lam hlam i

/-- **Dyadic strip power bound.**  On the strip `N ≤ x ≤ 2N` with `N ≥ 1`, the power
`x ^ (lam - i)` is at most `2 ^ lam * N ^ (lam - i)` for every nonnegative real `lam` and
every order `i`.

This is the report's `eq:power-strip-bound`.  The proof splits on the sign of `lam - i`:
for a nonnegative exponent the upper endpoint `x ≤ 2 * N` is used together with
`2 ^ (lam - i) ≤ 2 ^ lam`, and for a negative exponent the lower endpoint `N ≤ x` reverses
the monotonicity and `1 ≤ 2 ^ lam` absorbs the leading factor. -/
theorem rpow_le_of_mem_strip {N x lam : ℝ} (hN : 1 ≤ N) (h1 : N ≤ x) (h2 : x ≤ 2 * N)
    (hlam : 0 ≤ lam) (i : ℕ) :
    x ^ (lam - (i : ℝ)) ≤ (2 : ℝ) ^ lam * N ^ (lam - (i : ℝ)) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hNpos h1
  have hNr : (0 : ℝ) < N ^ (lam - (i : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  rcases le_or_gt 0 (lam - (i : ℝ)) with hsign | hsign
  · have hmono : (2 : ℝ) ^ (lam - (i : ℝ)) ≤ (2 : ℝ) ^ lam :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc x ^ (lam - (i : ℝ))
        ≤ (2 * N) ^ (lam - (i : ℝ)) := Real.rpow_le_rpow hxpos.le h2 hsign
      _ = (2 : ℝ) ^ (lam - (i : ℝ)) * N ^ (lam - (i : ℝ)) :=
          Real.mul_rpow (by norm_num) hNpos.le
      _ ≤ (2 : ℝ) ^ lam * N ^ (lam - (i : ℝ)) :=
          mul_le_mul_of_nonneg_right hmono hNr.le
  · have hone : (1 : ℝ) ≤ (2 : ℝ) ^ lam := Real.one_le_rpow (by norm_num) hlam
    calc x ^ (lam - (i : ℝ))
        ≤ N ^ (lam - (i : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hNpos h1 hsign.le
      _ = 1 * N ^ (lam - (i : ℝ)) := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ lam * N ^ (lam - (i : ℝ)) :=
          mul_le_mul_of_nonneg_right hone hNr.le

/-- **Combined divided-difference bound.**  The product of the two estimates above is the
report's `eq:dd-final-bound`: on the dyadic strip `1 ≤ N ≤ x ≤ 2N`, for `lam ≥ 0`,

```
  |(lam)_{\underline i}| / i ! * x ^ (lam - i) ≤ 2 ^ (2 * lam + i) * N ^ (lam - i).
```

Every mean-value point produced by the Newton divided-difference expansion of
`x ↦ x ^ lam` at nodes in `[N, 2N]` satisfies the hypotheses, so this bounds each Newton
row entry. -/
theorem abs_fallingRpowCoeff_div_factorial_mul_rpow_le
    {N x lam : ℝ} (hN : 1 ≤ N) (h1 : N ≤ x) (h2 : x ≤ 2 * N) (hlam : 0 ≤ lam) (i : ℕ) :
    |fallingRpowCoeff lam i| / (i ! : ℝ) * x ^ (lam - (i : ℝ))
      ≤ (2 : ℝ) ^ (2 * lam + (i : ℝ)) * N ^ (lam - (i : ℝ)) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hNpos h1
  have hcoeff := abs_fallingRpowCoeff_div_factorial_le lam hlam i
  have hstrip := rpow_le_of_mem_strip hN h1 h2 hlam i
  have hxnonneg : (0 : ℝ) ≤ x ^ (lam - (i : ℝ)) :=
    (Real.rpow_pos_of_pos hxpos _).le
  have hpownonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (lam + (i : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hprod :
      (2 : ℝ) ^ (lam + (i : ℝ)) * ((2 : ℝ) ^ lam * N ^ (lam - (i : ℝ)))
        = (2 : ℝ) ^ (2 * lam + (i : ℝ)) * N ^ (lam - (i : ℝ)) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show lam + (i : ℝ) + lam = 2 * lam + (i : ℝ) by ring]
  calc |fallingRpowCoeff lam i| / (i ! : ℝ) * x ^ (lam - (i : ℝ))
      ≤ (2 : ℝ) ^ (lam + (i : ℝ)) * ((2 : ℝ) ^ lam * N ^ (lam - (i : ℝ))) :=
        mul_le_mul hcoeff hstrip hxnonneg hpownonneg
    _ = (2 : ℝ) ^ (2 * lam + (i : ℝ)) * N ^ (lam - (i : ℝ)) := hprod

end LeanProofs.TwoBaseIntegerExponent
