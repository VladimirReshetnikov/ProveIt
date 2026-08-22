import ExponentialIdentities.TwoBaseIntegerExponent.CompactOrbit
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Exact denominator drift and local escape

For a normalized output `p ^ a * core = p ^ beta`, the denominator exponent at index `k` is
`floor (k * beta) - k * a`.  This module records its exact linear drift, the common bounded
fractional-part defect for two normalizations, and the resulting escape of the rational orbit
in the `p`-adic norm.

The integer-valued exponent is defined first, without a hidden truncating subtraction.  It is
converted to a natural number only after its nonnegativity has been proved.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Filter

noncomputable section

/-- The denominator exponent `floor(k * beta) - k * a`, kept in `ℤ` so that the
identity is unconditional.  Under the normalized-output hypotheses it is nonnegative. -/
def orbitDenominatorExponent (beta : ℝ) (a k : ℕ) : ℤ :=
  ⌊(k : ℝ) * beta⌋ - (k * a : ℕ)

/-- Exact linear drift plus the bounded fractional-part defect. -/
theorem orbitDenominatorExponent_cast (beta : ℝ) (a k : ℕ) :
    (orbitDenominatorExponent beta a k : ℝ) =
      (k : ℝ) * (beta - a) - Int.fract ((k : ℝ) * beta) := by
  rw [orbitDenominatorExponent, Int.cast_sub, Int.cast_natCast]
  rw [← Int.self_sub_floor ((k : ℝ) * beta)]
  push_cast
  ring

/-- After subtracting the linear drift, every denominator exponent has defect
`-fract(k * beta)`. -/
theorem orbitDenominatorExponent_centered (beta : ℝ) (a k : ℕ) :
    (orbitDenominatorExponent beta a k : ℝ) - (k : ℝ) * (beta - a) =
      -Int.fract ((k : ℝ) * beta) := by
  rw [orbitDenominatorExponent_cast]
  ring

/-- The two normalized denominator exponents have the same centered defect. -/
theorem orbitDenominatorExponent_common_defect (beta : ℝ) (a b k : ℕ) :
    (orbitDenominatorExponent beta a k : ℝ) - (k : ℝ) * (beta - a) =
      (orbitDenominatorExponent beta b k : ℝ) - (k : ℝ) * (beta - b) := by
  rw [orbitDenominatorExponent_centered, orbitDenominatorExponent_centered]

/-- Exact integral relation between the two denominator exponents. -/
theorem orbitDenominatorExponent_sub (beta : ℝ) (a b k : ℕ) :
    orbitDenominatorExponent beta a k - orbitDenominatorExponent beta b k =
      (k : ℤ) * ((b : ℤ) - (a : ℤ)) := by
  simp only [orbitDenominatorExponent]
  push_cast
  ring

/-- If the drift slope is nonnegative, the integer denominator exponent is nonnegative. -/
theorem orbitDenominatorExponent_nonneg {beta : ℝ} {a : ℕ}
    (ha : (a : ℝ) ≤ beta) (k : ℕ) :
    0 ≤ orbitDenominatorExponent beta a k := by
  have harg : 0 ≤ (k : ℝ) * (beta - a) :=
    mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr ha)
  have hfloor : 0 ≤ ⌊(k : ℝ) * (beta - a)⌋ := Int.floor_nonneg.mpr harg
  have heq : orbitDenominatorExponent beta a k = ⌊(k : ℝ) * (beta - a)⌋ := by
    rw [orbitDenominatorExponent]
    have hrewrite : (k : ℝ) * beta - ((k * a : ℕ) : ℝ) =
        (k : ℝ) * (beta - a) := by
      push_cast
      ring
    rw [← hrewrite]
    have hcast : (((k * a : ℕ) : ℝ)) = ((((k * a : ℕ) : ℤ) : ℝ)) := by
      norm_num
    rw [hcast, Int.floor_sub_intCast]
  rwa [heq]

/-- Natural-valued form of the denominator exponent. -/
def orbitDenominatorNat (beta : ℝ) (a k : ℕ) : ℕ :=
  (orbitDenominatorExponent beta a k).toNat

theorem orbitDenominatorNat_cast {beta : ℝ} {a : ℕ}
    (ha : (a : ℝ) ≤ beta) (k : ℕ) :
    (orbitDenominatorNat beta a k : ℤ) = orbitDenominatorExponent beta a k := by
  exact Int.toNat_of_nonneg (orbitDenominatorExponent_nonneg ha k)

theorem orbitDenominatorNat_cast_real {beta : ℝ} {a : ℕ}
    (ha : (a : ℝ) ≤ beta) (k : ℕ) :
    (orbitDenominatorNat beta a k : ℝ) =
      (k : ℝ) * (beta - a) - Int.fract ((k : ℝ) * beta) := by
  rw [← orbitDenominatorExponent_cast beta a k]
  exact_mod_cast orbitDenominatorNat_cast ha k

/-- A positive linear drift forces the natural denominator exponents to infinity. -/
theorem orbitDenominatorNat_tendsto_atTop {beta : ℝ} {a : ℕ}
    (ha : (a : ℝ) < beta) :
    Tendsto (orbitDenominatorNat beta a) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply Filter.tendsto_atTop.mpr
  intro R
  let slope : ℝ := beta - a
  have hslope : 0 < slope := sub_pos.mpr ha
  obtain ⟨K, hK⟩ := exists_nat_ge ((R + 1) / slope)
  apply Filter.eventually_atTop.mpr
  refine ⟨K, ?_⟩
  intro k hk
  rw [orbitDenominatorNat_cast_real ha.le]
  have hkcast : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hKmul : R + 1 ≤ (K : ℝ) * slope := by
    exact (div_le_iff₀ hslope).mp hK
  have hkmul : (K : ℝ) * slope ≤ (k : ℝ) * slope :=
    mul_le_mul_of_nonneg_right hkcast hslope.le
  have hfract := Int.fract_lt_one ((k : ℝ) * beta)
  change R ≤ (k : ℝ) * slope - Int.fract ((k : ℝ) * beta)
  linarith

/-- The rational normalized orbit with its base denominator removed. -/
def normalizedRationalOrbit
    (p core : ℕ) (beta : ℝ) (a k : ℕ) : ℚ :=
  (core : ℚ) ^ k / (p : ℚ) ^ orbitDenominatorNat beta a k

/-- If the numerator core is a `p`-adic unit, its normalized rational orbit has norm
exactly `p ^ q_k`. -/
theorem padicNorm_normalizedRationalOrbit
    {p core : ℕ} [Fact p.Prime] (hcore : ¬ p ∣ core)
    (beta : ℝ) (a k : ℕ) :
    padicNorm p (normalizedRationalOrbit p core beta a k) =
      (p : ℚ) ^ orbitDenominatorNat beta a k := by
  have hpow (x : ℚ) (n : ℕ) : padicNorm p (x ^ n) = (padicNorm p x) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, padicNorm.mul, ih]
  rw [normalizedRationalOrbit, padicNorm.div]
  rw [hpow, hpow]
  rw [(padicNorm.nat_eq_one_iff core).mpr hcore,
    padicNorm.padicNorm_p_of_prime]
  simp

/-- The `p`-adic norms of a normalized orbit escape to infinity whenever its denominator
exponent has positive drift. -/
theorem padicNorm_normalizedRationalOrbit_tendsto_atTop
    {p core : ℕ} [Fact p.Prime] (hcore : ¬ p ∣ core)
    {beta : ℝ} {a : ℕ} (ha : (a : ℝ) < beta) :
    Tendsto
      (fun k => padicNorm p (normalizedRationalOrbit p core beta a k))
      atTop atTop := by
  have hp : (1 : ℚ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hpow : Tendsto (fun n : ℕ => (p : ℚ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp
  have hcomp := hpow.comp (orbitDenominatorNat_tendsto_atTop ha)
  apply hcomp.congr'
  filter_upwards [] with k
  exact (padicNorm_normalizedRationalOrbit hcore beta a k).symm

/-- A nontrivial prime-free core forces the real exponent strictly beyond its base depth. -/
theorem baseDepth_lt_exponent_of_output
    {p a core : ℕ} {beta : ℝ} (hp : 1 < p) (hcore : 1 < core)
    (hout : (((p ^ a * core : ℕ) : ℝ)) = (p : ℝ) ^ beta) :
    (a : ℝ) < beta := by
  have hpowNat : p ^ a < p ^ a * core := by
    have hpos : 0 < p ^ a := pow_pos (Nat.zero_lt_of_lt hp) a
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hcore hpos
  have hpowReal : (p : ℝ) ^ (a : ℝ) < (p : ℝ) ^ beta := by
    rw [Real.rpow_natCast]
    rw [← hout]
    exact_mod_cast hpowNat
  exact (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hp)).lt_iff_lt.mp hpowReal

/-- Output normalization plus a prime-free core implies `p`-adic escape, with no separate
drift hypothesis required from the caller. -/
theorem padicNorm_normalizedRationalOrbit_tendsto_atTop_of_output
    {p a core : ℕ} [Fact p.Prime] {beta : ℝ}
    (hcoreUnit : ¬ p ∣ core) (hcore : 1 < core)
    (hout : (((p ^ a * core : ℕ) : ℝ)) = (p : ℝ) ^ beta) :
    Tendsto
      (fun k => padicNorm p (normalizedRationalOrbit p core beta a k))
      atTop atTop :=
  padicNorm_normalizedRationalOrbit_tendsto_atTop hcoreUnit
    (baseDepth_lt_exponent_of_output (Fact.out : Nat.Prime p).one_lt hcore hout)

/-- The two simultaneous primitive-output normalizations give both local escape statements. -/
theorem twoThree_padic_escape_of_normalized_outputs
    {a b W Z : ℕ} {beta : ℝ}
    (hWodd : Odd W) (hW : 1 < W) (hZunit : ¬ 3 ∣ Z) (hZ : 1 < Z)
    (hTwo : (((2 ^ a * W : ℕ) : ℝ)) = (2 : ℝ) ^ beta)
    (hThree : (((3 ^ b * Z : ℕ) : ℝ)) = (3 : ℝ) ^ beta) :
    Tendsto
        (fun k => padicNorm 2 (normalizedRationalOrbit 2 W beta a k))
        atTop atTop ∧
      Tendsto
        (fun k => padicNorm 3 (normalizedRationalOrbit 3 Z beta b k))
        atTop atTop := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨
    padicNorm_normalizedRationalOrbit_tendsto_atTop_of_output
      hWodd.not_two_dvd_nat hW hTwo,
    padicNorm_normalizedRationalOrbit_tendsto_atTop_of_output
      hZunit hZ hThree⟩

end

end LeanProofs.TwoBaseIntegerExponent
