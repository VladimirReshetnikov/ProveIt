import FabiusFunction.ThueMorseMasterProduct

/-!
# The Woods–Robbins product

The classical evaluation
`∏ ((2n+1)/(2n+2))^(ε(n)) = 1/√2`, by the atlas's pairing argument
made rigorous in logarithmic form: the three log-series

`L_A = ∑ ε(n)·log((2n+1)/(2n+2))`,
`L_B = ∑_{n≥1} ε(n)·log(2n/(2n+1))`,
`L_C = ∑_{n≥1} ε(n)·log(n/(n+1))`

converge by Dirichlet's test; termwise `L_A + L_B = -log 2 + L_C`,
and interleaving the even-length partials of `L_C` through
`ε(2j) = ε(j)`, `ε(2j+1) = -ε(j)` gives `L_C = L_B - L_A`.  Hence
`L_A = -(log 2)/2`, and exponentiating evaluates the product.

The first of the three is not a new series: `wrA` *is* the master log-series
`mpLog` of `ThueMorseMasterProduct` at the parameters `(1/2, 1)`, termwise,
because `(n+1/2)/(n+1) = (2n+1)/(2n+2)`.  Its convergence is therefore the
`(1/2, 1)` instance of `mpLog_cauchy`, and the evaluation below identifies the
master limit there.  Only `wrB` and `wrC`, which are guarded at `n = 0`
because their parameter `a` degenerates to `0`, need their own treatment.

* `wrA`, `wrB`, `wrC` — the three partial log-sums.
* `mpLog_one_half_eq_wrA` — `wrA` is the master log-series at `(1/2, 1)`.
* `tendsto_wrA` — `L_A = -(log 2)/2`.
* `mpLimit_one_half_one` — hence `L(1/2, 1) = -(log 2)/2`, the one closed
  value of the master series the atlas pins down directly.
* `woods_robbins` — **the product evaluation** (`thm:Woods-Robbins`).
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- Partial sums of the Woods–Robbins log-series. -/
noncomputable def wrA (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (thueMorseSign n : ℝ) *
    Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))

/-- Partial sums of the companion even-ratio series (guarded at 0). -/
noncomputable def wrB (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (thueMorseSign n : ℝ) *
    (if n = 0 then 0 else Real.log ((2 * (n : ℝ)) / (2 * (n : ℝ) + 1)))

/-- Partial sums of the collapsed ratio series (guarded at 0). -/
noncomputable def wrC (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (thueMorseSign n : ℝ) *
    (if n = 0 then 0 else Real.log ((n : ℝ) / ((n : ℝ) + 1)))

/-- `log(1 + 1/g) → 0` when `g → ∞`. -/
private theorem tendsto_log_one_add_inv (g : ℕ → ℝ)
    (hg : Tendsto g atTop atTop) :
    Tendsto (fun n => Real.log (1 + 1 / g n)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n => 1 / g n) atTop (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_) hg.inv_tendsto_atTop
    rw [Pi.inv_apply, one_div]
  have h1 : Tendsto (fun n => 1 + 1 / g n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h3
  have h2 := ((Real.continuousAt_log
    (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp h1
  rw [Real.log_one] at h2
  exact h2

/-- Dirichlet's test for a sign-weighted series with a weight that is
antitone from `1` on and tends to zero (guarded at `0`). -/
private theorem cauchySeq_guarded (f : ℕ → ℝ)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → f n ≤ f m)
    (hlim : Tendsto f atTop (𝓝 0)) :
    CauchySeq (fun N => ∑ n ∈ range N, (thueMorseSign n : ℝ) *
      (if n = 0 then 0 else f n)) := by
  have hshift : CauchySeq (fun K => ∑ k ∈ range K,
      f (k + 1) • (thueMorseSign (k + 1) : ℝ)) := by
    refine Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      (fun p q hpq => hmono (p + 1) (q + 1) (by omega) (by omega))
      (hlim.comp (tendsto_add_atTop_nat 1)) (b := 2) ?_
    intro K
    have h1 := norm_sum_thueMorseSign_le_one (K + 1)
    have h2 : ∑ k ∈ range K, (thueMorseSign (k + 1) : ℝ) =
        (∑ n ∈ range (K + 1), (thueMorseSign n : ℝ)) -
          (thueMorseSign 0 : ℝ) := by
      rw [Finset.sum_range_succ']
      ring
    rw [h2]
    have h3 : ‖(thueMorseSign 0 : ℝ)‖ ≤ 1 := by
      norm_num [thueMorseSign, binaryWeight]
    calc ‖(∑ n ∈ range (K + 1), (thueMorseSign n : ℝ)) -
          (thueMorseSign 0 : ℝ)‖
        ≤ ‖∑ n ∈ range (K + 1), (thueMorseSign n : ℝ)‖ +
            ‖(thueMorseSign 0 : ℝ)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hkey : (fun K => ∑ n ∈ range (K + 1),
      (thueMorseSign n : ℝ) * (if n = 0 then 0 else f n)) =
      fun K => ∑ k ∈ range K,
        f (k + 1) • (thueMorseSign (k + 1) : ℝ) := by
    funext K
    rw [Finset.sum_range_succ']
    rw [if_pos rfl, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_neg (by omega), smul_eq_mul]
    ring
  rw [← cauchySeq_shift 1]
  show CauchySeq (fun K => ∑ n ∈ range (K + 1),
    (thueMorseSign n : ℝ) * (if n = 0 then 0 else f n))
  rw [hkey]
  exact hshift

/-- **The Woods--Robbins series is the master series at `(1/2, 1)`.**
Termwise `log((n+1/2)/(n+1)) = log((2n+1)/(2n+2))`: the two ratios agree
after clearing denominators. -/
theorem mpLog_one_half_eq_wrA (N : ℕ) :
    mpLog (1 / 2 : ℝ) 1 N = wrA N := by
  rw [mpLog, wrA]
  refine Finset.sum_congr rfl fun n _ => ?_
  have harg : ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) =
      (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [harg]

/-- Convergence of the Woods--Robbins partials is the `(1/2, 1)` instance of
`mpLog_cauchy`; no separate Dirichlet-test argument is needed. -/
private theorem wrA_cauchy : CauchySeq wrA := by
  have h := mpLog_cauchy (1 / 2 : ℝ) 1 (by norm_num) (by norm_num)
  rwa [funext mpLog_one_half_eq_wrA] at h

private theorem wrB_cauchy : CauchySeq wrB := by
  have hneg : wrB = fun N => -∑ n ∈ range N,
      (thueMorseSign n : ℝ) *
        (if n = 0 then 0 else
          Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ)))) := by
    funext N
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg (by omega), if_neg (by omega),
        show (2 * (n : ℝ) + 1) / (2 * (n : ℝ)) =
          ((2 * (n : ℝ)) / (2 * (n : ℝ) + 1))⁻¹ from by
            rw [inv_div],
        Real.log_inv]
      ring
  rw [hneg]
  refine CauchySeq.neg ?_
  refine cauchySeq_guarded _ ?_ ?_
  · intro m n hm hmn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h := le_trans hm hmn
      exact_mod_cast h
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hle : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    nlinarith
  · refine (tendsto_log_one_add_inv (fun n => 2 * (n : ℝ))
      ((tendsto_natCast_atTop_atTop).const_mul_atTop
        (by norm_num))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < 2 * (n : ℝ) := by linarith
    congr 1
    field_simp

private theorem wrC_cauchy : CauchySeq wrC := by
  have hneg : wrC = fun N => -∑ n ∈ range N,
      (thueMorseSign n : ℝ) *
        (if n = 0 then 0 else
          Real.log (((n : ℝ) + 1) / (n : ℝ))) := by
    funext N
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg (by omega), if_neg (by omega),
        show ((n : ℝ) + 1) / (n : ℝ) =
          ((n : ℝ) / ((n : ℝ) + 1))⁻¹ from by
            rw [inv_div],
        Real.log_inv]
      ring
  rw [hneg]
  refine CauchySeq.neg ?_
  refine cauchySeq_guarded _ ?_ ?_
  · intro m n hm hmn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h := le_trans hm hmn
      exact_mod_cast h
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hle : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    nlinarith
  · refine (tendsto_log_one_add_inv (fun n => (n : ℝ))
      tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < (n : ℝ) := by linarith
    congr 1
    field_simp

noncomputable def wrLimitA : ℝ := limUnder atTop wrA

private theorem tendsto_wrA_limit :
    Tendsto wrA atTop (𝓝 wrLimitA) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete wrA_cauchy
  rwa [wrLimitA, hL.limUnder_eq]

noncomputable def wrLimitB : ℝ := limUnder atTop wrB

private theorem tendsto_wrB_limit :
    Tendsto wrB atTop (𝓝 wrLimitB) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete wrB_cauchy
  rwa [wrLimitB, hL.limUnder_eq]

noncomputable def wrLimitC : ℝ := limUnder atTop wrC

private theorem tendsto_wrC_limit :
    Tendsto wrC atTop (𝓝 wrLimitC) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete wrC_cauchy
  rwa [wrLimitC, hL.limUnder_eq]

/-- Termwise combination: `wrA + wrB = -log 2 + wrC` for `N ≥ 1`. -/
private theorem wrA_add_wrB (N : ℕ) (hN : 1 ≤ N) :
    wrA N + wrB N = -Real.log 2 + wrC N := by
  rw [wrA, wrB, wrC, ← Finset.sum_add_distrib]
  have hterm : ∀ n ∈ range N,
      (thueMorseSign n : ℝ) *
          Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) +
        (thueMorseSign n : ℝ) *
          (if n = 0 then 0 else
            Real.log ((2 * (n : ℝ)) / (2 * (n : ℝ) + 1))) =
      (if n = 0 then -Real.log 2 else 0) +
        (thueMorseSign n : ℝ) *
          (if n = 0 then 0 else Real.log ((n : ℝ) / ((n : ℝ) + 1))) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [mul_zero, Nat.cast_zero]
      have hsign : (thueMorseSign 0 : ℝ) = 1 := by
        norm_num [thueMorseSign, binaryWeight]
      rw [hsign, one_mul]
      norm_num
      rw [one_div, Real.log_inv]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        zero_add, ← mul_add,
        ← Real.log_mul (by positivity) (by positivity)]
      congr 2
      field_simp
      try ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' (range N) 0 (fun _ => -Real.log 2),
    if_pos (Finset.mem_range.mpr (by omega))]

/-- Interleaving: `wrC (2N) = wrB N - wrA N`. -/
private theorem wrC_two_mul (N : ℕ) :
    wrC (2 * N) = wrB N - wrA N := by
  rw [wrC, sum_range_two_mul]
  have hterm : ∀ j ∈ range N,
      ((thueMorseSign (2 * j) : ℝ) *
          (if 2 * j = 0 then 0 else
            Real.log (((2 * j : ℕ) : ℝ) / (((2 * j : ℕ) : ℝ) + 1))) +
        (thueMorseSign (2 * j + 1) : ℝ) *
          (if 2 * j + 1 = 0 then 0 else
            Real.log (((2 * j + 1 : ℕ) : ℝ) /
              (((2 * j + 1 : ℕ) : ℝ) + 1)))) =
      (thueMorseSign j : ℝ) *
          (if j = 0 then 0 else
            Real.log ((2 * (j : ℝ)) / (2 * (j : ℝ) + 1))) -
        (thueMorseSign j : ℝ) *
          Real.log ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) := by
    intro j _
    have hsign1 : (thueMorseSign (2 * j) : ℝ) =
        (thueMorseSign j : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ))
        (thueMorseSign_two_mul j)
    have hsign2 : (thueMorseSign (2 * j + 1) : ℝ) =
        -(thueMorseSign j : ℝ) := by
      have h := thueMorseSign_two_mul_add_one j
      push_cast [h]
      ring
    rw [hsign1, hsign2, if_neg (by omega : ¬ 2 * j + 1 = 0)]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [mul_zero, zero_add]
      push_cast
      ring_nf
    · rw [if_neg (by omega : ¬ 2 * j = 0), if_neg (by omega)]
      push_cast
      ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, wrA, wrB]

/-- The limit of the Woods–Robbins log-series is `-(log 2)/2`. -/
theorem tendsto_wrA : Tendsto wrA atTop (𝓝 (-Real.log 2 / 2)) := by
  have hA := tendsto_wrA_limit
  have hB := tendsto_wrB_limit
  have hC := tendsto_wrC_limit
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => (by omega : n ≤ 2 * n)) tendsto_id
  have h1 : Tendsto (fun N => wrC (2 * N)) atTop (𝓝 wrLimitC) :=
    hC.comp hdouble
  have h2 : Tendsto (fun N => wrB N - wrA N) atTop
      (𝓝 (wrLimitB - wrLimitA)) := hB.sub hA
  have hCBA : wrLimitC = wrLimitB - wrLimitA := by
    refine tendsto_nhds_unique ?_ h2
    exact h1.congr fun N => wrC_two_mul N
  have h3 : Tendsto (fun N => wrA N + wrB N) atTop
      (𝓝 (wrLimitA + wrLimitB)) := hA.add hB
  have h4 : Tendsto (fun N => -Real.log 2 + wrC N) atTop
      (𝓝 (-Real.log 2 + wrLimitC)) := tendsto_const_nhds.add hC
  have hABC : wrLimitA + wrLimitB = -Real.log 2 + wrLimitC := by
    refine tendsto_nhds_unique ?_ h4
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact wrA_add_wrB N hN
  have hval : wrLimitA = -Real.log 2 / 2 := by
    rw [hCBA] at hABC
    linarith
  rw [← hval]
  exact hA

/-- The master log-series has the closed value `-(log 2)/2` at the parameters
`(1/2, 1)`: it is the Woods--Robbins series there, and `tendsto_wrA` evaluates
it.  This is the only closed value of `L(a,b)` the atlas pins down without an
auxiliary product identity. -/
theorem mpLimit_one_half_one :
    mpLimit (1 / 2 : ℝ) 1 = -Real.log 2 / 2 :=
  tendsto_nhds_unique
    (tendsto_mpLimit (1 / 2 : ℝ) 1 (by norm_num) (by norm_num))
    (tendsto_wrA.congr fun N => (mpLog_one_half_eq_wrA N).symm)

/-- **The Woods–Robbins product** (`thm:Woods-Robbins`):
`∏_{n<N} ((2n+1)/(2n+2))^(ε(n)) ⟶ 1/√2`. -/
theorem woods_robbins :
    Tendsto (fun N => ∏ n ∈ range N,
      ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) ^ (thueMorseSign n))
      atTop (𝓝 (1 / Real.sqrt 2)) := by
  rw [← exp_neg_log_div_two (by norm_num : (0 : ℝ) < 2)]
  exact tendsto_prod_zpow_of_tendsto_sum (fun N : ℕ => range N)
    (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) thueMorseSign
    (fun n => by positivity) tendsto_wrA

end Fabius
