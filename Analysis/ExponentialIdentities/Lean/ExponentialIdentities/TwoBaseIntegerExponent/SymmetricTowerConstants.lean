import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicBaseUnitPower
import ExponentialIdentities.TwoBaseIntegerExponent.SmoothOutputs
import ExponentialIdentities.TwoBaseIntegerExponent.Localization
import ExponentialIdentities.TwoBaseIntegerExponent.MultiplicativeRank
import ExponentialIdentities.TwoBaseIntegerExponent.RadicalReformulation

/-!
# The symmetric tower constants `E₃ = 3 ^ θ` and `E₂ = 2 ^ η`

Write `θ = log 3 / log 2` (`logThreeDivLogTwo`) and `η = 1 / θ = log 2 / log 3`
(`logTwoDivLogThree`).  The two *symmetric tower constants* are

```
E₃ = 3 ^ θ = 5.7045224946911176…,      E₂ = 2 ^ η = 1.5485626526302429… .
```

`E₃` is the canonical radical of the smooth branch in which the primitive odd core of the
first output equals `3`, and `E₂` is its base-swapped mirror.  Neither number is known to be
transcendental, and for `E₃` even irrationality is open.  What *is* available unconditionally
is a statement about the **pair**.

Three groups of results are proved here.

* Elementary size and duality facts: `3 < E₃`, `1 < E₂ < 2`, and the swap identities
  `E₃ ^ η = 3`, `E₂ ^ θ = 2`, alongside `2 ^ θ = 3` and `3 ^ η = 2`.

* The exact conditional link to the smooth branches.  If `x` is a nonintegral two-base
  solution whose first output is three-smooth, `2 ^ x = 2 ^ a * 3 ^ b`, then necessarily
  `b > 0` and `E₃ ^ b = 3 ^ x / 3 ^ a = n / 3 ^ a`, a positive rational, so `E₃` is an
  explicit algebraic radical; symmetrically a three-smooth second output
  `3 ^ x = 2 ^ c * 3 ^ d` forces `c > 0` and `E₂ ^ c = m / 2 ^ d`.  Both directions are
  proved: algebraicity of `E₃` is *equivalent* to three-smoothness of `m = 2 ^ x`, and
  algebraicity of `E₂` to three-smoothness of `n = 3 ^ x`.  The forward implications use the
  corpus six-exponentials theorem for the bases `2, 3, m` at the exponent `θ` (respectively
  `2, 3, n` at the exponent `η`); the auxiliary identities `m ^ θ = n` and `n ^ η = m` supply
  the third algebraic value.

* The headline dichotomy: `E₃` and `E₂` cannot both be algebraic.  Two independent proofs are
  given.  The *unconditional* one,
  `not_isAlgebraic_symmetricTowerThree_and_symmetricTowerTwo`, runs six exponentials on the
  bases `2, 3, E₂` at the exponent `θ`, whose six values are `2, 3, E₂, 3, E₃, 2`; the
  monomial-independence hypothesis is discharged by
  `not_hasPositiveTwoThreeUnitPower_symmetricTowerTwo`, since a rational `2,3`-unit power of
  `E₂` would exhibit `θ` as a root of a rational quadratic with nonzero constant term.  The
  *branch* proof,
  `TwoBaseNonintegerSolution.not_isAlgebraic_symmetricTowerThree_and_symmetricTowerTwo`,
  instead combines the two branch classifications with `integer_of_threeSmooth_outputs`: two
  algebraic tower constants would make both outputs three-smooth, and a two-base solution
  with two three-smooth outputs has integral exponent.

Nothing here proves that `E₃` or `E₂` is individually transcendental; a counterexample to the
Alaoglu--Erdős conjecture would make exactly one of them an explicit algebraic radical.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set
open LeanProofs.AlgebraicSixExponentials

noncomputable section

/-! ### The two constants -/

/-- The symmetric tower constant `E₃ = 3 ^ (log 3 / log 2)`. -/
def symmetricTowerThree : ℝ := (3 : ℝ) ^ logThreeDivLogTwo

/-- The symmetric tower constant `E₂ = 2 ^ (log 2 / log 3) = 2 ^ (1 / θ)`. -/
def symmetricTowerTwo : ℝ := (2 : ℝ) ^ logTwoDivLogThree

/-- Definitional unfolding of `E₃`. -/
theorem symmetricTowerThree_def :
    symmetricTowerThree = (3 : ℝ) ^ logThreeDivLogTwo := rfl

/-- Definitional unfolding of `E₂`. -/
theorem symmetricTowerTwo_def :
    symmetricTowerTwo = (2 : ℝ) ^ logTwoDivLogThree := rfl

private theorem log_two_ne_zero' : Real.log 2 ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

private theorem log_three_ne_zero' : Real.log 3 ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))

/-! ### The exponents `θ` and `η` -/

/-- The swapped exponent is the reciprocal of `θ`. -/
theorem logTwoDivLogThree_eq_inv : logTwoDivLogThree = logThreeDivLogTwo⁻¹ := by
  rw [logTwoDivLogThree, logThreeDivLogTwo, inv_div]

/-- The swapped exponent written as `1 / θ`, the form used in the report. -/
theorem logTwoDivLogThree_eq_one_div :
    logTwoDivLogThree = 1 / logThreeDivLogTwo := by
  rw [logTwoDivLogThree_eq_inv, one_div]

/-- `θ` and `η` are reciprocal. -/
theorem logThreeDivLogTwo_mul_logTwoDivLogThree :
    logThreeDivLogTwo * logTwoDivLogThree = 1 := by
  have hl2 : Real.log 2 ≠ 0 := log_two_ne_zero'
  have hl3 : Real.log 3 ≠ 0 := log_three_ne_zero'
  rw [logThreeDivLogTwo, logTwoDivLogThree]
  field_simp

/-- `η` and `θ` are reciprocal. -/
theorem logTwoDivLogThree_mul_logThreeDivLogTwo :
    logTwoDivLogThree * logThreeDivLogTwo = 1 := by
  rw [mul_comm]
  exact logThreeDivLogTwo_mul_logTwoDivLogThree

/-- The swapped exponent is positive. -/
theorem logTwoDivLogThree_pos : 0 < logTwoDivLogThree := by
  rw [logTwoDivLogThree]
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- The swapped exponent is smaller than one. -/
theorem logTwoDivLogThree_lt_one : logTwoDivLogThree < 1 := by
  rw [logTwoDivLogThree]
  exact (div_lt_one (Real.log_pos (by norm_num))).2
    (Real.log_lt_log (by norm_num) (by norm_num))

/-- The swapped exponent is irrational, because `θ` is. -/
theorem irrational_logTwoDivLogThree : Irrational logTwoDivLogThree := by
  rw [logTwoDivLogThree_eq_inv]
  exact irrational_inv_iff.mpr irrational_logThreeDivLogTwo

/-- The base-swap identity `3 ^ η = 2`, dual to `2 ^ θ = 3`. -/
theorem three_rpow_logTwoDivLogThree_eq_two :
    (3 : ℝ) ^ logTwoDivLogThree = 2 := by
  rw [← two_rpow_logThreeDivLogTwo, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    logThreeDivLogTwo_mul_logTwoDivLogThree, Real.rpow_one]

/-! ### Elementary size and duality facts -/

/-- `E₃` is positive. -/
theorem symmetricTowerThree_pos : 0 < symmetricTowerThree :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- `E₂` is positive. -/
theorem symmetricTowerTwo_pos : 0 < symmetricTowerTwo :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- `E₃ = 3 ^ θ` exceeds `3`, because `θ > 1`. -/
theorem three_lt_symmetricTowerThree : (3 : ℝ) < symmetricTowerThree := by
  rw [symmetricTowerThree_def]
  have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2
    one_lt_logThreeDivLogTwo
  rwa [Real.rpow_one] at h

/-- `E₃ > 1`. -/
theorem one_lt_symmetricTowerThree : 1 < symmetricTowerThree :=
  lt_trans (by norm_num) three_lt_symmetricTowerThree

/-- `E₂ = 2 ^ η > 1`, because `η > 0`. -/
theorem one_lt_symmetricTowerTwo : 1 < symmetricTowerTwo := by
  rw [symmetricTowerTwo_def]
  have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
    logTwoDivLogThree_pos
  rwa [Real.rpow_zero] at h

/-- `E₂ < 2`, because `η < 1`. -/
theorem symmetricTowerTwo_lt_two : symmetricTowerTwo < 2 := by
  rw [symmetricTowerTwo_def]
  have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
    logTwoDivLogThree_lt_one
  rwa [Real.rpow_one] at h

/-- `E₂ = 2 ^ (1 / θ)`, the form used in the report. -/
theorem symmetricTowerTwo_eq_two_rpow_one_div :
    symmetricTowerTwo = (2 : ℝ) ^ (1 / logThreeDivLogTwo) := by
  rw [symmetricTowerTwo_def, logTwoDivLogThree_eq_one_div]

/-- The swap identity `E₃ ^ η = 3`. -/
theorem symmetricTowerThree_rpow_logTwoDivLogThree :
    symmetricTowerThree ^ logTwoDivLogThree = 3 := by
  rw [symmetricTowerThree_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    logThreeDivLogTwo_mul_logTwoDivLogThree, Real.rpow_one]

/-- The swap identity `E₂ ^ θ = 2`. -/
theorem symmetricTowerTwo_rpow_logThreeDivLogTwo :
    symmetricTowerTwo ^ logThreeDivLogTwo = 2 := by
  rw [symmetricTowerTwo_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    logTwoDivLogThree_mul_logThreeDivLogTwo, Real.rpow_one]

private theorem three_rpow_natCast_mul_theta (b : ℕ) :
    (3 : ℝ) ^ ((b : ℝ) * logThreeDivLogTwo) = symmetricTowerThree ^ b := by
  rw [symmetricTowerThree_def, ← Real.rpow_natCast ((3 : ℝ) ^ logThreeDivLogTwo) b,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_comm logThreeDivLogTwo (b : ℝ)]

private theorem two_rpow_natCast_mul_eta (c : ℕ) :
    (2 : ℝ) ^ ((c : ℝ) * logTwoDivLogThree) = symmetricTowerTwo ^ c := by
  rw [symmetricTowerTwo_def, ← Real.rpow_natCast ((2 : ℝ) ^ logTwoDivLogThree) c,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm logTwoDivLogThree (c : ℝ)]

/-! ### Having a positive rational power -/

/-- A real number has a positive rational power when one of its positive natural powers is a
positive rational number.  This is the exact form in which a smooth branch produces its
symmetric tower constant. -/
def HasPositiveRationalPower (gamma : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ q : ℚ, 0 < q ∧ gamma ^ n = (q : ℝ)

/-- A positive rational power makes the number algebraic. -/
theorem HasPositiveRationalPower.isAlgebraic {gamma : ℝ}
    (h : HasPositiveRationalPower gamma) : IsAlgebraic ℚ gamma := by
  obtain ⟨n, hn, q, _hq, hpow⟩ := h
  refine IsAlgebraic.of_pow hn ?_
  rw [hpow]
  exact isAlgebraic_rat ℚ q

/-! ### The smooth branches -/

private theorem exponent_eq_of_two_rpow_smooth {x : ℝ} {a b : ℕ}
    (h : (2 : ℝ) ^ x = (2 : ℝ) ^ a * (3 : ℝ) ^ b) :
    x = (a : ℝ) + (b : ℝ) * logThreeDivLogTwo := by
  have hl2 : Real.log 2 ≠ 0 := log_two_ne_zero'
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [logThreeDivLogTwo]
  field_simp
  linarith [hlog]

private theorem exponent_eq_of_three_rpow_smooth {x : ℝ} {c d : ℕ}
    (h : (3 : ℝ) ^ x = (2 : ℝ) ^ c * (3 : ℝ) ^ d) :
    x = (d : ℝ) + (c : ℝ) * logTwoDivLogThree := by
  have hl3 : Real.log 3 ≠ 0 := log_three_ne_zero'
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [logTwoDivLogThree]
  field_simp
  linarith [hlog]

/-- **The `E₃` branch.**  If the first output of a nonintegral two-base solution is
three-smooth, `2 ^ x = 2 ^ a * 3 ^ b`, then the exponent of three is positive and the second
output splits as `3 ^ x = 3 ^ a * E₃ ^ b`. -/
theorem TwoBaseNonintegerSolution.three_rpow_eq_of_two_rpow_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {a b : ℕ}
    (hsmooth : (2 : ℝ) ^ x = (2 : ℝ) ^ a * (3 : ℝ) ^ b) :
    0 < b ∧ (3 : ℝ) ^ x = (3 : ℝ) ^ a * symmetricTowerThree ^ b := by
  have hxeq : x = (a : ℝ) + (b : ℝ) * logThreeDivLogTwo :=
    exponent_eq_of_two_rpow_smooth hsmooth
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · exfalso
      apply hx.2
      refine ⟨(a : ℤ), ?_⟩
      rw [hxeq, hb]
      push_cast <;> ring
    · exact hb
  · rw [hxeq, Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast,
      three_rpow_natCast_mul_theta]

/-- **The `E₂` branch.**  If the second output of a nonintegral two-base solution is
three-smooth, `3 ^ x = 2 ^ c * 3 ^ d`, then the exponent of two is positive and the first
output splits as `2 ^ x = 2 ^ d * E₂ ^ c`. -/
theorem TwoBaseNonintegerSolution.two_rpow_eq_of_three_rpow_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {c d : ℕ}
    (hsmooth : (3 : ℝ) ^ x = (2 : ℝ) ^ c * (3 : ℝ) ^ d) :
    0 < c ∧ (2 : ℝ) ^ x = (2 : ℝ) ^ d * symmetricTowerTwo ^ c := by
  have hxeq : x = (d : ℝ) + (c : ℝ) * logTwoDivLogThree :=
    exponent_eq_of_three_rpow_smooth hsmooth
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · exfalso
      apply hx.2
      refine ⟨(d : ℤ), ?_⟩
      rw [hxeq, hc]
      push_cast <;> ring
    · exact hc
  · rw [hxeq, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast,
      two_rpow_natCast_mul_eta]

/-- **The explicit `E₃` radical.**  In the smooth branch `2 ^ x = 2 ^ a * 3 ^ b` of a
nonintegral solution with second output `n`, the exponent `b` is positive and
`E₃ ^ b = n / 3 ^ a`, an explicit positive rational. -/
theorem TwoBaseNonintegerSolution.symmetricTowerThree_pow_eq
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {a b n : ℕ}
    (hsmooth : (2 : ℝ) ^ x = (2 : ℝ) ^ a * (3 : ℝ) ^ b)
    (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    0 < b ∧ symmetricTowerThree ^ b = (n : ℝ) / (3 : ℝ) ^ a := by
  obtain ⟨hb, hthree⟩ := hx.three_rpow_eq_of_two_rpow_threeSmooth hsmooth
  have h3a : ((3 : ℝ) ^ a) ≠ 0 := by positivity
  refine ⟨hb, ?_⟩
  rw [hn, hthree, eq_div_iff h3a]
  ring

/-- **The explicit `E₂` radical.**  In the smooth branch `3 ^ x = 2 ^ c * 3 ^ d` of a
nonintegral solution with first output `m`, the exponent `c` is positive and
`E₂ ^ c = m / 2 ^ d`. -/
theorem TwoBaseNonintegerSolution.symmetricTowerTwo_pow_eq
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {c d m : ℕ}
    (hsmooth : (3 : ℝ) ^ x = (2 : ℝ) ^ c * (3 : ℝ) ^ d)
    (hm : (m : ℝ) = (2 : ℝ) ^ x) :
    0 < c ∧ symmetricTowerTwo ^ c = (m : ℝ) / (2 : ℝ) ^ d := by
  obtain ⟨hc, htwo⟩ := hx.two_rpow_eq_of_three_rpow_threeSmooth hsmooth
  have h2d : ((2 : ℝ) ^ d) ≠ 0 := by positivity
  refine ⟨hc, ?_⟩
  rw [hm, htwo, eq_div_iff h2d]
  ring

private theorem exists_natCast_eq_rpow {b x : ℝ} (hb : 0 < b)
    (h : b ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∃ k : ℕ, (k : ℝ) = b ^ x ∧ 0 < k := by
  obtain ⟨z, hz⟩ := h
  have hpos : (0 : ℝ) < (z : ℝ) := by
    rw [hz]
    exact Real.rpow_pos_of_pos hb x
  have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast hpos.le
  have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz0
  have hkpos : (0 : ℝ) < ((z.toNat : ℕ) : ℝ) := by
    rw [hcast]
    exact hpos
  refine ⟨z.toNat, ?_, by exact_mod_cast hkpos⟩
  rw [hcast]
  exact hz

/-- The smooth branch produces a positive rational power of `E₃`. -/
theorem TwoBaseNonintegerSolution.hasPositiveRationalPower_symmetricTowerThree
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hsmooth : IsThreeSmoothReal ((2 : ℝ) ^ x)) :
    HasPositiveRationalPower symmetricTowerThree := by
  obtain ⟨a, b, hab⟩ := hsmooth
  obtain ⟨n, hn, hnpos⟩ := exists_natCast_eq_rpow (by norm_num : (0 : ℝ) < 3) hx.1.2
  obtain ⟨hb, hpow⟩ := hx.symmetricTowerThree_pow_eq hab hn
  refine ⟨b, hb, (n : ℚ) / (3 : ℚ) ^ a, ?_, ?_⟩
  · exact div_pos (by exact_mod_cast hnpos) (by positivity)
  · rw [hpow]
    push_cast <;> ring

/-- The mirrored smooth branch produces a positive rational power of `E₂`. -/
theorem TwoBaseNonintegerSolution.hasPositiveRationalPower_symmetricTowerTwo
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hsmooth : IsThreeSmoothReal ((3 : ℝ) ^ x)) :
    HasPositiveRationalPower symmetricTowerTwo := by
  obtain ⟨c, d, hcd⟩ := hsmooth
  obtain ⟨m, hm, hmpos⟩ := exists_natCast_eq_rpow (by norm_num : (0 : ℝ) < 2) hx.1.1
  obtain ⟨hc, hpow⟩ := hx.symmetricTowerTwo_pow_eq hcd hm
  refine ⟨c, hc, (m : ℚ) / (2 : ℚ) ^ d, ?_, ?_⟩
  · exact div_pos (by exact_mod_cast hmpos) (by positivity)
  · rw [hpow]
    push_cast <;> ring

/-- In the smooth branch of a nonintegral solution, `E₃` is algebraic. -/
theorem TwoBaseNonintegerSolution.isAlgebraic_symmetricTowerThree_of_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hsmooth : IsThreeSmoothReal ((2 : ℝ) ^ x)) :
    IsAlgebraic ℚ symmetricTowerThree :=
  (hx.hasPositiveRationalPower_symmetricTowerThree hsmooth).isAlgebraic

/-- In the mirrored smooth branch of a nonintegral solution, `E₂` is algebraic. -/
theorem TwoBaseNonintegerSolution.isAlgebraic_symmetricTowerTwo_of_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hsmooth : IsThreeSmoothReal ((3 : ℝ) ^ x)) :
    IsAlgebraic ℚ symmetricTowerTwo :=
  (hx.hasPositiveRationalPower_symmetricTowerTwo hsmooth).isAlgebraic

/-! ### Six exponentials in the two tower configurations -/

private theorem rational_of_two_three_and_base
    {c : ℝ} (hc : 0 < c) (hcAlg : IsAlgebraic ℚ c)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2.1 * c ^ u.2.2))
    {y : ℝ} (hTwo : IsAlgebraic ℚ ((2 : ℝ) ^ y))
    (hThree : IsAlgebraic ℚ ((3 : ℝ) ^ y)) (hBase : IsAlgebraic ℚ (c ^ y)) :
    y ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_of_three_real_rpows_isAlgebraic_of_monomial_injective
    (a := (2 : ℝ)) (b := (3 : ℝ)) (c := c) (by norm_num) (by norm_num) hc
    (isAlgebraic_nat 2) (isAlgebraic_nat 3) hcAlg hmono hTwo hThree hBase

private theorem natCast_rpow_theta {x : ℝ} {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    (m : ℝ) ^ logThreeDivLogTwo = (n : ℝ) := by
  rw [hm, hn, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm x logThreeDivLogTwo, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    two_rpow_logThreeDivLogTwo]

private theorem natCast_rpow_eta {x : ℝ} {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    (n : ℝ) ^ logTwoDivLogThree = (m : ℝ) := by
  rw [hn, hm, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    mul_comm x logTwoDivLogThree, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    three_rpow_logTwoDivLogThree_eq_two]

private theorem threeSmooth_of_unitPower_natCast
    {m : ℕ} (hm : 0 < m) (h : HasPositiveTwoThreeUnitPower (m : ℝ)) :
    ∃ a b : ℕ, m = 2 ^ a * 3 ^ b := by
  obtain ⟨N, hN, q, _hqpos, ⟨i, j, k, l, hq⟩, hpow⟩ := h
  have hqrat : ((m : ℚ)) ^ N = q := by
    have hcast : (((m : ℚ) ^ N : ℚ) : ℝ) = ((q : ℚ) : ℝ) := by
      push_cast
      exact hpow
    exact_mod_cast hcast
  have hden : (((2 ^ k * 3 ^ l : ℕ)) : ℚ) ≠ 0 := by positivity
  have hprod : (m : ℚ) ^ N * ((2 ^ k * 3 ^ l : ℕ) : ℚ) = ((2 ^ i * 3 ^ j : ℕ) : ℚ) := by
    rw [hqrat, hq]
    field_simp
  have hnat : m ^ N * (2 ^ k * 3 ^ l) = 2 ^ i * 3 ^ j := by exact_mod_cast hprod
  rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hm]
  intro p hp hpm
  have hpdvd : p ∣ 2 ^ i * 3 ^ j := by
    rw [← hnat]
    exact dvd_mul_of_dvd_left (dvd_pow hpm hN.ne') _
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))

/-- **Six exponentials in the `E₃` configuration.**  If `E₃ = 3 ^ θ` is algebraic, then the
first output `m = 2 ^ x` of a two-base solution is three-smooth.

The six values are `2, 3, m, 2 ^ θ = 3, 3 ^ θ = E₃, m ^ θ = n`; the third one is available
precisely because `m ^ θ = (2 ^ x) ^ θ = (2 ^ θ) ^ x = 3 ^ x = n`.  No nonintegrality
hypothesis is needed. -/
theorem threeSmooth_two_rpow_of_isAlgebraic_symmetricTowerThree
    {x : ℝ} {m n : ℕ} (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x)
    (hE3 : IsAlgebraic ℚ symmetricTowerThree) :
    ∃ a b : ℕ, m = 2 ^ a * 3 ^ b := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    rw [hm]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hmpos : 0 < m := by exact_mod_cast hmR
  by_cases hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2.1 * (m : ℝ) ^ u.2.2)
  · exfalso
    have hE3' : IsAlgebraic ℚ ((3 : ℝ) ^ logThreeDivLogTwo) := hE3
    have hTwo : IsAlgebraic ℚ ((2 : ℝ) ^ logThreeDivLogTwo) := by
      rw [two_rpow_logThreeDivLogTwo]
      exact isAlgebraic_nat 3
    have hBase : IsAlgebraic ℚ ((m : ℝ) ^ logThreeDivLogTwo) := by
      rw [natCast_rpow_theta hm hn]
      exact isAlgebraic_nat n
    exact irrational_logThreeDivLogTwo
      (rational_of_two_three_and_base hmR (isAlgebraic_nat m) hmono hTwo hE3' hBase)
  · have hunit : HasPositiveTwoThreeUnitPower (m : ℝ) := by
      by_contra hno
      exact hmono ((real_two_three_gamma_monomial_injective_iff hmR).2 hno)
    exact threeSmooth_of_unitPower_natCast hmpos hunit

/-- **Six exponentials in the `E₂` configuration.**  If `E₂ = 2 ^ η` is algebraic, then the
second output `n = 3 ^ x` of a two-base solution is three-smooth.

The six values are `2, 3, n, 2 ^ η = E₂, 3 ^ η = 2, n ^ η = m`. -/
theorem threeSmooth_three_rpow_of_isAlgebraic_symmetricTowerTwo
    {x : ℝ} {m n : ℕ} (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x)
    (hE2 : IsAlgebraic ℚ symmetricTowerTwo) :
    ∃ c d : ℕ, n = 2 ^ c * 3 ^ d := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    rw [hn]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hnpos : 0 < n := by exact_mod_cast hnR
  by_cases hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2.1 * (n : ℝ) ^ u.2.2)
  · exfalso
    have hE2' : IsAlgebraic ℚ ((2 : ℝ) ^ logTwoDivLogThree) := hE2
    have hThree : IsAlgebraic ℚ ((3 : ℝ) ^ logTwoDivLogThree) := by
      rw [three_rpow_logTwoDivLogThree_eq_two]
      exact isAlgebraic_nat 2
    have hBase : IsAlgebraic ℚ ((n : ℝ) ^ logTwoDivLogThree) := by
      rw [natCast_rpow_eta hm hn]
      exact isAlgebraic_nat m
    exact irrational_logTwoDivLogThree
      (rational_of_two_three_and_base hnR (isAlgebraic_nat n) hmono hE2' hThree hBase)
  · have hunit : HasPositiveTwoThreeUnitPower (n : ℝ) := by
      by_contra hno
      exact hmono ((real_two_three_gamma_monomial_injective_iff hnR).2 hno)
    exact threeSmooth_of_unitPower_natCast hnpos hunit

/-- **Exact `E₃` branch classification.**  For a nonintegral two-base solution, `E₃` is
algebraic exactly when the first output is three-smooth. -/
theorem TwoBaseNonintegerSolution.isAlgebraic_symmetricTowerThree_iff_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    IsAlgebraic ℚ symmetricTowerThree ↔ ∃ a b : ℕ, m = 2 ^ a * 3 ^ b := by
  constructor
  · intro hE3
    exact threeSmooth_two_rpow_of_isAlgebraic_symmetricTowerThree hm hn hE3
  · rintro ⟨a, b, hab⟩
    refine hx.isAlgebraic_symmetricTowerThree_of_threeSmooth ⟨a, b, ?_⟩
    rw [← hm, hab]
    push_cast <;> ring

/-- **Exact `E₂` branch classification.**  For a nonintegral two-base solution, `E₂` is
algebraic exactly when the second output is three-smooth. -/
theorem TwoBaseNonintegerSolution.isAlgebraic_symmetricTowerTwo_iff_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ x) (hn : (n : ℝ) = (3 : ℝ) ^ x) :
    IsAlgebraic ℚ symmetricTowerTwo ↔ ∃ c d : ℕ, n = 2 ^ c * 3 ^ d := by
  constructor
  · intro hE2
    exact threeSmooth_three_rpow_of_isAlgebraic_symmetricTowerTwo hm hn hE2
  · rintro ⟨c, d, hcd⟩
    refine hx.isAlgebraic_symmetricTowerTwo_of_threeSmooth ⟨c, d, ?_⟩
    rw [← hn, hcd]
    push_cast <;> ring

/-! ### The unconditional dichotomy -/

/-- `θ` is not a root of a rational quadratic with nonzero constant term. -/
private theorem no_rational_quadratic_of_const_ne_zero {α β γ : ℚ} (hγ : γ ≠ 0)
    (h : (α : ℝ) * logThreeDivLogTwo ^ 2 + (β : ℝ) * logThreeDivLogTwo + (γ : ℝ) = 0) :
    False := by
  apply transcendental_logThreeDivLogTwo
  refine ⟨Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X +
      Polynomial.C γ, ?_, ?_⟩
  · intro hzero
    apply hγ
    have hev := congrArg (fun p : Polynomial ℚ ↦ p.eval 0) hzero
    simpa using hev
  · simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      eq_ratCast]
    linarith [h]

/-- **No positive power of `E₂` is a rational `2,3`-unit.**  Such a power would exhibit `θ`
as a root of a rational quadratic with nonzero constant term, contradicting the
kernel-verified transcendence of `θ`. -/
theorem not_hasPositiveTwoThreeUnitPower_symmetricTowerTwo :
    ¬ HasPositiveTwoThreeUnitPower symmetricTowerTwo := by
  rintro ⟨N, hN, q, _hqpos, ⟨i, j, k, l, hq⟩, hpow⟩
  have hl2 : Real.log 2 ≠ 0 := log_two_ne_zero'
  rw [symmetricTowerTwo_def] at hpow
  have hpow' : (2 : ℝ) ^ (logTwoDivLogThree * (N : ℝ)) = (q : ℝ) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    exact hpow
  have hqR : (q : ℝ) = (2 : ℝ) ^ i * (3 : ℝ) ^ j / ((2 : ℝ) ^ k * (3 : ℝ) ^ l) := by
    rw [hq]
    push_cast <;> ring
  have hlog := congrArg Real.log hpow'
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), hqR,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlog' : logTwoDivLogThree * (N : ℝ) * Real.log 2 =
      ((i : ℝ) - (k : ℝ)) * Real.log 2 + ((j : ℝ) - (l : ℝ)) * Real.log 3 := by
    linear_combination hlog
  have hL3 : Real.log 3 = logThreeDivLogTwo * Real.log 2 := by
    rw [logThreeDivLogTwo]
    field_simp
  rw [hL3] at hlog'
  have hlin : logTwoDivLogThree * (N : ℝ) =
      ((i : ℝ) - (k : ℝ)) + ((j : ℝ) - (l : ℝ)) * logThreeDivLogTwo :=
    mul_right_cancel₀ hl2 (by linear_combination hlog')
  have hquad : ((j : ℝ) - (l : ℝ)) * logThreeDivLogTwo ^ 2 +
      ((i : ℝ) - (k : ℝ)) * logThreeDivLogTwo + (-(N : ℝ)) = 0 := by
    linear_combination (-logThreeDivLogTwo) * hlin +
      (N : ℝ) * logTwoDivLogThree_mul_logThreeDivLogTwo
  refine no_rational_quadratic_of_const_ne_zero
    (α := ((j : ℚ) - (l : ℚ))) (β := ((i : ℚ) - (k : ℚ))) (γ := (-(N : ℚ))) ?_ ?_
  · exact neg_ne_zero.2 (Nat.cast_ne_zero.2 hN.ne')
  · push_cast
    linear_combination hquad

/-- **At least one symmetric tower constant is transcendental.**  Unconditionally, `E₃` and
`E₂` are not both algebraic.

This is the ordinary-algebraicity form of the report's unconditional dichotomy.  The six
exponentials theorem is applied to the bases `2, 3, E₂` at the exponent `θ`, whose six values
are `2, 3, E₂, 2 ^ θ = 3, 3 ^ θ = E₃, E₂ ^ θ = 2`. -/
theorem not_isAlgebraic_symmetricTowerThree_and_symmetricTowerTwo :
    ¬ (IsAlgebraic ℚ symmetricTowerThree ∧ IsAlgebraic ℚ symmetricTowerTwo) := by
  rintro ⟨h3, h2⟩
  have hmono := (real_two_three_gamma_monomial_injective_iff symmetricTowerTwo_pos).2
    not_hasPositiveTwoThreeUnitPower_symmetricTowerTwo
  have hE3' : IsAlgebraic ℚ ((3 : ℝ) ^ logThreeDivLogTwo) := h3
  have hTwo : IsAlgebraic ℚ ((2 : ℝ) ^ logThreeDivLogTwo) := by
    rw [two_rpow_logThreeDivLogTwo]
    exact isAlgebraic_nat 3
  have hBase : IsAlgebraic ℚ (symmetricTowerTwo ^ logThreeDivLogTwo) := by
    rw [symmetricTowerTwo_rpow_logThreeDivLogTwo]
    exact isAlgebraic_nat 2
  exact irrational_logThreeDivLogTwo
    (rational_of_two_three_and_base symmetricTowerTwo_pos h2 hmono hTwo hE3' hBase)

/-- The rational-power form of the unconditional dichotomy: `E₃` and `E₂` cannot both have a
positive rational power. -/
theorem not_hasPositiveRationalPower_symmetricTowerThree_and_symmetricTowerTwo :
    ¬ (HasPositiveRationalPower symmetricTowerThree ∧
        HasPositiveRationalPower symmetricTowerTwo) := by
  rintro ⟨h3, h2⟩
  exact not_isAlgebraic_symmetricTowerThree_and_symmetricTowerTwo
    ⟨h3.isAlgebraic, h2.isAlgebraic⟩

/-- **The two symmetric branches are mutually exclusive.**  Under a hypothetical nonintegral
two-base solution, `E₃` and `E₂` cannot both be algebraic.

This is the report's branch proof: algebraicity of `E₃` makes `2 ^ x` three-smooth and
algebraicity of `E₂` makes `3 ^ x` three-smooth, and
`integer_of_two_three_rpow_integer_of_threeSmooth_outputs` forbids two three-smooth outputs
at a nonintegral exponent. -/
theorem TwoBaseNonintegerSolution.not_isAlgebraic_symmetricTowerThree_and_symmetricTowerTwo
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ¬ (IsAlgebraic ℚ symmetricTowerThree ∧ IsAlgebraic ℚ symmetricTowerTwo) := by
  rintro ⟨h3, h2⟩
  obtain ⟨m, hm, _hmpos⟩ := exists_natCast_eq_rpow (by norm_num : (0 : ℝ) < 2) hx.1.1
  obtain ⟨n, hn, _hnpos⟩ := exists_natCast_eq_rpow (by norm_num : (0 : ℝ) < 3) hx.1.2
  exact hx.2 (integer_of_two_three_rpow_integer_of_threeSmooth_outputs hm hn
    (threeSmooth_two_rpow_of_isAlgebraic_symmetricTowerThree hm hn h3)
    (threeSmooth_three_rpow_of_isAlgebraic_symmetricTowerTwo hm hn h2))

/-- **At most one output of a counterexample is three-smooth.**  For a nonintegral two-base
solution at most one of the two smooth branches can occur, so at most one of `E₃`, `E₂` is an
explicit algebraic radical. -/
theorem TwoBaseNonintegerSolution.not_both_threeSmooth_outputs
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ¬ (IsThreeSmoothReal ((2 : ℝ) ^ x) ∧ IsThreeSmoothReal ((3 : ℝ) ^ x)) := by
  rintro ⟨h2, h3⟩
  exact hx.2 (integer_of_threeSmooth_outputs h2 h3)

end

end LeanProofs.TwoBaseIntegerExponent
