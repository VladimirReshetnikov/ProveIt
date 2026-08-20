import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Algebra.Order.Round

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- Every positive natural multiple of a hypothetical nonintegral solution stays an
explicit logarithmic distance from both endpoints of its unit interval. -/
theorem multiple_fract_log_gaps
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) :
    let y := (k : ℝ) * x
    let n := ⌊y⌋.toNat
    Real.logb 2 (1 + 1 / (2 : ℝ) ^ n) ≤ Int.fract y ∧
      1 - Real.logb 2 (2 - 1 / (2 : ℝ) ^ n) ≤ 1 - Int.fract y := by
  dsimp only
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  have hy0 : 0 ≤ (k : ℝ) * x := mul_nonneg (by positivity) hx0
  have hyirr : Irrational ((k : ℝ) * x) :=
    (irrational_of_not_integer_of_two_rpow_integer hx h₂).natCast_mul hk.ne'
  have hfloor0 : 0 ≤ ⌊(k : ℝ) * x⌋ := Int.floor_nonneg.mpr hy0
  have hfloor_cast :
      ((⌊(k : ℝ) * x⌋.toNat : ℕ) : ℝ) = (⌊(k : ℝ) * x⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfloor0
  have ht0 : 0 < Int.fract ((k : ℝ) * x) := by
    rw [Int.fract_pos]
    exact hyirr.ne_int _
  have ht1 : Int.fract ((k : ℝ) * x) < 1 := Int.fract_lt_one _
  have hdecomp :
      ((⌊(k : ℝ) * x⌋.toNat : ℕ) : ℝ) + Int.fract ((k : ℝ) * x) =
        (k : ℝ) * x := by
    rw [hfloor_cast, Int.floor_add_fract]
  have hint : ∃ z : ℤ, (z : ℝ) =
      (2 : ℝ) ^ (((⌊(k : ℝ) * x⌋.toNat : ℕ) : ℝ) +
        Int.fract ((k : ℝ) * x)) := by
    rw [hdecomp]
    simpa using rpow_integer_nat_mul (b := 2) h₂ k
  have hgap := rpow_fractional_part_gap (b := 2) (n := ⌊(k : ℝ) * x⌋.toNat)
    (by norm_num) ht0 ht1 hint
  have hp1 : 1 ≤ (2 : ℝ) ^ ⌊(k : ℝ) * x⌋.toNat := one_le_pow₀ (by norm_num)
  have hinv1 : 1 / (2 : ℝ) ^ ⌊(k : ℝ) * x⌋.toNat ≤ 1 := by
    exact (div_le_one (by positivity)).2 hp1
  have huppos : 0 < 2 - 1 / (2 : ℝ) ^ ⌊(k : ℝ) * x⌋.toNat := by
    linarith
  constructor
  · exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).2 hgap.1
  · have hu := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) huppos).2 hgap.2
    linarith

/-- The radius of the dyadic shrinking target forced by an integral power of two.
It is asymptotic to `2 ^ (-y) / (2 * log 2)` as `y → ∞`. -/
noncomputable def dyadicShrinkingRadius (y : ℝ) : ℝ :=
  1 - Real.logb 2 (2 - 1 / (2 : ℝ) ^ y)

/-- A simpler exponential lower bound for the exact dyadic radius. -/
theorem half_inv_two_rpow_le_dyadicShrinkingRadius {y : ℝ} (hy : 0 ≤ y) :
    1 / (2 * (2 : ℝ) ^ y) ≤ dyadicShrinkingRadius y := by
  let v : ℝ := 1 / (2 : ℝ) ^ y
  have hpow1 : 1 ≤ (2 : ℝ) ^ y :=
    Real.one_le_rpow (by norm_num) hy
  have hv0 : 0 < v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp only [v]
    exact (div_le_one (by positivity)).2 hpow1
  let q : ℝ := 1 - v / 2
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have hfactor : 2 - v = 2 * q := by dsimp only [q]; ring
  have hlogq : Real.log q ≤ -v / 2 := by
    have := Real.log_le_sub_one_of_pos hq0
    dsimp only [q] at this
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmul : v / 2 * Real.log 2 ≤ v / 2 := by
    exact mul_le_of_le_one_right (by positivity) hlog2le
  have hradius : dyadicShrinkingRadius y = -Real.log q / Real.log 2 := by
    rw [dyadicShrinkingRadius, Real.logb, hfactor,
      Real.log_mul (by norm_num) hq0.ne']
    field_simp
    ring
  rw [hradius]
  have hvhalf : v / 2 ≤ -Real.log q / Real.log 2 := by
    apply (le_div_iff₀ hlog2pos).2
    linarith
  have hv_eq : 1 / (2 * (2 : ℝ) ^ y) = v / 2 := by
    dsimp only [v]
    ring
  rw [hv_eq]
  exact hvhalf

/-- Quantitative shrinking-target obstruction.  If `x` were a nonintegral solution, then
for every `k ≥ 1`, the fractional part of `k*x` is at least
`dyadicShrinkingRadius (k*x)` away from both `0` and `1`. -/
theorem multiple_fract_dyadic_shrinking_target
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) :
    dyadicShrinkingRadius ((k : ℝ) * x) ≤
      min (Int.fract ((k : ℝ) * x)) (1 - Int.fract ((k : ℝ) * x)) := by
  rw [le_min_iff]
  have hgaps := multiple_fract_log_gaps hx h₂ k hk
  let y : ℝ := (k : ℝ) * x
  let n : ℕ := ⌊y⌋.toNat
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  have hy0 : 0 ≤ y := mul_nonneg (by positivity) hx0
  have hfloor0 : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
  have hn_cast : (n : ℝ) = (⌊y⌋ : ℝ) := by
    dsimp only [n]
    exact_mod_cast Int.toNat_of_nonneg hfloor0
  have hny : (n : ℝ) ≤ y := hn_cast.trans_le (Int.floor_le y)
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ y := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hny
  let u : ℝ := 1 / (2 : ℝ) ^ n
  let v : ℝ := 1 / (2 : ℝ) ^ y
  have hu0 : 0 < u := by dsimp only [u]; positivity
  have hv0 : 0 < v := by dsimp only [v]; positivity
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hvu : v ≤ u := by
    dsimp only [v, u]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hargu0 : 0 < 2 - u := by linarith
  have hargv0 : 0 < 2 - v := by linarith
  have hratio : 2 / (2 - u) ≤ 1 + u := by
    apply (div_le_iff₀ hargu0).2
    nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hu1)]
  have hlogratio : Real.logb 2 (2 / (2 - u)) ≤ Real.logb 2 (1 + u) :=
    Real.logb_le_logb_of_le (by norm_num) (div_pos (by norm_num) hargu0) hratio
  rw [Real.logb_div (by norm_num) hargu0.ne',
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlogratio
  have hargmono : Real.logb 2 (2 - u) ≤ Real.logb 2 (2 - v) :=
    Real.logb_le_logb_of_le (by norm_num) hargu0 (sub_le_sub_left hvu 2)
  change 1 - Real.logb 2 (2 - v) ≤ Int.fract y ∧
    1 - Real.logb 2 (2 - v) ≤ 1 - Int.fract y
  constructor
  · calc
      1 - Real.logb 2 (2 - v) ≤ 1 - Real.logb 2 (2 - u) := by linarith
      _ ≤ Real.logb 2 (1 + u) := hlogratio
      _ ≤ Int.fract y := by simpa only [y, n, u] using hgaps.1
  · calc
      1 - Real.logb 2 (2 - v) ≤ 1 - Real.logb 2 (2 - u) := by linarith
      _ ≤ 1 - Int.fract y := by simpa only [y, n, u] using hgaps.2

/-- The analogous exact shrinking radius for an arbitrary natural base. -/
noncomputable def baseShrinkingRadius (b : ℕ) (y : ℝ) : ℝ :=
  1 - Real.logb (b : ℝ) ((b : ℝ) - 1 / (b : ℝ) ^ y)

/-- General-base form of the shrinking-target argument.  The integral power of two is used
only to know that the nonintegral exponent, and hence every positive natural multiple, is
irrational; `hbase` supplies the endpoint gaps at base `b`. -/
theorem multiple_fract_base_shrinking_target
    {b : ℕ} (hb : 1 < b) {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hbase : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) :
    baseShrinkingRadius b ((k : ℝ) * x) ≤
      min (Int.fract ((k : ℝ) * x)) (1 - Int.fract ((k : ℝ) * x)) := by
  let y : ℝ := (k : ℝ) * x
  let n : ℕ := ⌊y⌋.toNat
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  have hy0 : 0 ≤ y := mul_nonneg (by positivity) hx0
  have hyirr : Irrational y := by
    exact (irrational_of_not_integer_of_two_rpow_integer hx h₂).natCast_mul hk.ne'
  have hfloor0 : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
  have hn_cast : (n : ℝ) = (⌊y⌋ : ℝ) := by
    dsimp only [n]
    exact_mod_cast Int.toNat_of_nonneg hfloor0
  have ht0 : 0 < Int.fract y := by
    rw [Int.fract_pos]
    exact hyirr.ne_int _
  have ht1 : Int.fract y < 1 := Int.fract_lt_one _
  have hdecomp : (n : ℝ) + Int.fract y = y := by
    rw [hn_cast, Int.floor_add_fract]
  have hint : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ ((n : ℝ) + Int.fract y) := by
    rw [hdecomp]
    simpa only [y] using rpow_integer_nat_mul hbase k
  have hgap := rpow_fractional_part_gap (b := b) (n := n) hb ht0 ht1 hint
  let u : ℝ := 1 / (b : ℝ) ^ n
  let v : ℝ := 1 / (b : ℝ) ^ y
  have hu0 : 0 < u := by dsimp only [u]; positivity
  have hv0 : 0 < v := by dsimp only [v]; positivity
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hbR.le)
  have hny : (n : ℝ) ≤ y := hn_cast.trans_le (Int.floor_le y)
  have hpow : (b : ℝ) ^ n ≤ (b : ℝ) ^ y := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbR.le hny
  have hvu : v ≤ u := by
    dsimp only [v, u]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
  have hargu0 : 0 < (b : ℝ) - u := by linarith
  have hargv0 : 0 < (b : ℝ) - v := by linarith
  have hubm1 : u ≤ (b : ℝ) - 1 := by linarith
  have hratio : (b : ℝ) / ((b : ℝ) - u) ≤ 1 + u := by
    apply (div_le_iff₀ hargu0).2
    nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hubm1)]
  have hlogratio :
      Real.logb (b : ℝ) ((b : ℝ) / ((b : ℝ) - u)) ≤
        Real.logb (b : ℝ) (1 + u) :=
    Real.logb_le_logb_of_le hbR (div_pos (by positivity) hargu0) hratio
  rw [Real.logb_div (by positivity) hargu0.ne',
    Real.logb_self_eq_one hbR] at hlogratio
  have hargmono :
      Real.logb (b : ℝ) ((b : ℝ) - u) ≤
        Real.logb (b : ℝ) ((b : ℝ) - v) :=
    Real.logb_le_logb_of_le hbR hargu0 (sub_le_sub_left hvu _)
  have hlowlog : Real.logb (b : ℝ) (1 + u) ≤ Int.fract y := by
    exact (Real.logb_le_iff_le_rpow hbR (by positivity)).2 (by simpa only [u] using hgap.1)
  have huplog :
      1 - Real.logb (b : ℝ) ((b : ℝ) - u) ≤ 1 - Int.fract y := by
    have hle := (Real.le_logb_iff_rpow_le hbR hargu0).2 (by simpa only [u] using hgap.2)
    linarith
  rw [le_min_iff]
  change 1 - Real.logb (b : ℝ) ((b : ℝ) - v) ≤ Int.fract y ∧
    1 - Real.logb (b : ℝ) ((b : ℝ) - v) ≤ 1 - Int.fract y
  constructor
  · calc
      1 - Real.logb (b : ℝ) ((b : ℝ) - v) ≤
          1 - Real.logb (b : ℝ) ((b : ℝ) - u) := by linarith
      _ ≤ Real.logb (b : ℝ) (1 + u) := hlogratio
      _ ≤ Int.fract y := hlowlog
  · calc
      1 - Real.logb (b : ℝ) ((b : ℝ) - v) ≤
          1 - Real.logb (b : ℝ) ((b : ℝ) - u) := by linarith
      _ ≤ 1 - Int.fract y := huplog

/-- Simultaneous exact obstruction from the two integral bases. -/
theorem two_three_multiple_fract_shrinking_target
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) :
    max (baseShrinkingRadius 2 ((k : ℝ) * x))
        (baseShrinkingRadius 3 ((k : ℝ) * x)) ≤
      min (Int.fract ((k : ℝ) * x)) (1 - Int.fract ((k : ℝ) * x)) := by
  rw [max_le_iff]
  exact ⟨multiple_fract_base_shrinking_target (by norm_num) hx h₂ h₂ k hk,
    multiple_fract_base_shrinking_target (by norm_num) hx h₂ h₃ k hk⟩

/-- Simultaneous two-base distance-to-any-integer form. -/
theorem two_three_multiple_distance_to_integer_lower_bound
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) (p : ℤ) :
    max (baseShrinkingRadius 2 ((k : ℝ) * x))
        (baseShrinkingRadius 3 ((k : ℝ) * x)) ≤
      |(k : ℝ) * x - (p : ℝ)| := by
  calc
    max (baseShrinkingRadius 2 ((k : ℝ) * x))
        (baseShrinkingRadius 3 ((k : ℝ) * x)) ≤
        min (Int.fract ((k : ℝ) * x)) (1 - Int.fract ((k : ℝ) * x)) :=
      two_three_multiple_fract_shrinking_target hx h₂ h₃ k hk
    _ = |(k : ℝ) * x - (round ((k : ℝ) * x) : ℝ)| :=
      (abs_sub_round_eq_min _).symm
    _ ≤ |(k : ℝ) * x - (p : ℝ)| := round_le _ p

/-- Simultaneous two-base rational-approximation form. -/
theorem two_three_rational_approximation_lower_bound
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) (p : ℤ) :
    max (baseShrinkingRadius 2 ((k : ℝ) * x))
          (baseShrinkingRadius 3 ((k : ℝ) * x)) / (k : ℝ) ≤
      |x - (p : ℝ) / (k : ℝ)| := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := two_three_multiple_distance_to_integer_lower_bound hx h₂ h₃ k hk p
  have heq : (k : ℝ) * x - (p : ℝ) =
      (k : ℝ) * (x - (p : ℝ) / (k : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hkR] at h
  exact (div_le_iff₀ hkR).2 (by simpa [mul_comm] using h)

/-- Distance-to-any-integer form of the shrinking-target obstruction. -/
theorem multiple_distance_to_integer_lower_bound
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) (p : ℤ) :
    dyadicShrinkingRadius ((k : ℝ) * x) ≤ |(k : ℝ) * x - (p : ℝ)| := by
  calc
    dyadicShrinkingRadius ((k : ℝ) * x) ≤
        min (Int.fract ((k : ℝ) * x)) (1 - Int.fract ((k : ℝ) * x)) :=
      multiple_fract_dyadic_shrinking_target hx h₂ k hk
    _ = |(k : ℝ) * x - (round ((k : ℝ) * x) : ℝ)| :=
      (abs_sub_round_eq_min _).symm
    _ ≤ |(k : ℝ) * x - (p : ℝ)| := round_le _ p

/-- Rational-approximation form: a hypothetical nonintegral solution cannot be approximated
by a rational `p/k` more closely than the displayed exponentially shrinking radius. -/
theorem rational_approximation_lower_bound
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) (p : ℤ) :
    dyadicShrinkingRadius ((k : ℝ) * x) / (k : ℝ) ≤
      |x - (p : ℝ) / (k : ℝ)| := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := multiple_distance_to_integer_lower_bound hx h₂ k hk p
  have heq : (k : ℝ) * x - (p : ℝ) =
      (k : ℝ) * (x - (p : ℝ) / (k : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hkR] at h
  exact (div_le_iff₀ hkR).2 (by simpa [mul_comm] using h)

/-- A conventional, slightly weaker exponential Diophantine bound obtained from the exact
shrinking radius. -/
theorem rational_approximation_exponential_lower_bound
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (k : ℕ) (hk : 0 < k) (p : ℤ) :
    1 / (2 * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) * x)) ≤
      |x - (p : ℝ) / (k : ℝ)| := by
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  have hy0 : 0 ≤ (k : ℝ) * x := mul_nonneg (by positivity) hx0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr := half_inv_two_rpow_le_dyadicShrinkingRadius hy0
  have ha := rational_approximation_lower_bound hx h₂ k hk p
  calc
    1 / (2 * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) * x)) =
        (1 / (2 * (2 : ℝ) ^ ((k : ℝ) * x))) / (k : ℝ) := by field_simp
    _ ≤ dyadicShrinkingRadius ((k : ℝ) * x) / (k : ℝ) :=
      div_le_div_of_nonneg_right hr hkR.le
    _ ≤ |x - (p : ℝ) / (k : ℝ)| := ha

/-- Arithmetic form of the preceding result.  Writing the integral value `2^x` as the
positive natural number `m`, all rational approximations have error at least
`1 / (2*k*m^k)`. -/
theorem exists_natural_base_rational_approximation_lower_bound
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) = (2 : ℝ) ^ x ∧
      ∀ (k : ℕ), 0 < k → ∀ p : ℤ,
        1 / (2 * (k : ℝ) * (m : ℝ) ^ k) ≤
          |x - (p : ℝ) / (k : ℝ)| := by
  obtain ⟨z, hz⟩ := h₂
  have hzpos : 0 < z := by
    exact_mod_cast (hz.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
  norm_num at hz hzpos
  have hm : 0 < m := by exact_mod_cast hzpos
  refine ⟨m, hm, hz, ?_⟩
  intro k hk p
  have h := rational_approximation_exponential_lower_bound hx ⟨m, hz⟩ k hk p
  have hpow : (2 : ℝ) ^ ((k : ℝ) * x) = (m : ℝ) ^ k := by
    calc
      (2 : ℝ) ^ ((k : ℝ) * x) = (2 : ℝ) ^ (x * (k : ℝ)) := by rw [mul_comm]
      _ = ((2 : ℝ) ^ x) ^ k :=
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) x k
      _ = (m : ℝ) ^ k := by rw [← hz]
  simpa only [hpow] using h

end LeanProofs.TwoBaseIntegerExponent
