import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicBaseUnitPower
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicConsequences
import ExponentialIdentities.TwoBaseIntegerExponent.SmoothOutputs

/-!
# Depth-three tower rigidity at the base two

For positive real bases the iterated power tower is unambiguous,
`((γ ^ x) ^ x) ^ x = γ ^ (x ^ 3)`, so a hypothetical nonintegral two-base solution `x` can be
applied to a fixed algebraic base repeatedly and one may ask how long algebraicity survives.
This module formalizes the base-two instance of that question, which the unified report
records as the *base-two tower dichotomy* and the *base-two cubic-tower equivalence*.

Write `M = 2 ^ x` and `A = 3 ^ x` for the two integral outputs of a counterexample.  The
three results below are:

* **Level two, three-smooth branch.**  If `M = 2 ^ a * 3 ^ b`, then
  `2 ^ (x * x) = M ^ x = (2 ^ x) ^ a * (3 ^ x) ^ b = M ^ a * A ^ b`, an explicit natural
  number written in the two original outputs with the exponents that describe the first
  output.  This is an unconditional identity: no nonintegrality hypothesis is used.
* **Level two, dichotomy.**  For a nonintegral solution, `2 ^ (x * x)` is algebraic exactly
  when `M` is three-smooth.  The proof runs `2 ^ (x * x) = M ^ x` into the natural-base
  classification of `AlgebraicConsequences`; the same statement is also recorded through the
  algebraic-base spectrum theorem of `AlgebraicBaseUnitPower`, via the bridge lemma
  `hasPositiveTwoThreeUnitPower_natCast_iff` identifying, for a positive natural number,
  the predicate `HasPositiveTwoThreeUnitPower` with three-smoothness.
* **Level three.**  In the three-smooth branch the second level is a natural number, but the
  third level `2 ^ (x * x * x)` is transcendental: the base `M ^ a * A ^ b` of that last step
  is *not* three-smooth, because `b > 0` and the partner output `A` is forced to carry a prime
  factor at least `5` by `exists_prime_five_le_dvd_of_threeSmooth_candidate`.

Combining the two branches gives a base-two three-level detector: the Alaoglu--Erdős
conjecture is equivalent to algebraicity of `2 ^ (x ^ 2)` together with `2 ^ (x ^ 3)` at every
two-base integral-power solution.  One original base suffices if one is willing to climb one
extra level, in place of the two-base second-level tests of `AlgebraicConsequences`.

Everything here is the ordinary-transcendence shadow of the report's statements.  The report
additionally asserts that the offending logarithm escapes the `ℚ̄`-span of logarithms of
algebraic numbers; that stronger form rests on Baker's theorem and Roy's strong six
exponentials theorem, neither of which is available in this repository, and is *not* proved
here.
-/

open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-! ### Elementary helpers -/

/-- An integral positive power is represented by a positive natural number. -/
private theorem exists_pos_nat_eq_rpow {c : ℝ} (hc : 0 < c) {x : ℝ}
    (h : c ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) = c ^ x := by
  obtain ⟨z, hz⟩ := h
  have hzpos : (0 : ℤ) < z := by
    have hreal : (0 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact Real.rpow_pos_of_pos hc x
    exact_mod_cast hreal
  have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hzpos.le
  refine ⟨z.toNat, by omega, ?_⟩
  rw [hcast]
  exact hz

/-- A pure power of two as the value of `2 ^ x` pins the exponent to that natural number. -/
private theorem eq_natCast_of_two_rpow_eq_two_pow {x : ℝ} {a : ℕ}
    (h : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ x) :
    x = (a : ℝ) := by
  have hcast : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast] at h
  have hlog := congrArg Real.log h
  rw [Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact (mul_right_cancel₀ hne hlog).symm

/-- An algebraic base has algebraic real power at every integral exponent. -/
private theorem algebraic_rpow_of_integer_exponent
    {gamma x : ℝ} (hgammaAlg : IsAlgebraic ℚ gamma)
    (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ (gamma ^ x) := by
  obtain ⟨z, rfl⟩ := hx
  rw [Real.rpow_intCast]
  cases z with
  | ofNat n => simpa using hgammaAlg.pow n
  | negSucc n =>
      rw [zpow_negSucc]
      exact (hgammaAlg.pow (n + 1)).inv

/-- The integral reals are closed under multiplication. -/
private theorem mul_mem_range_intCast {x y : ℝ}
    (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (hy : y ∈ Set.range ((↑) : ℤ → ℝ)) :
    x * y ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨m * n, by rw [Int.cast_mul]⟩

/-! ### The bridge between the spectrum predicate and three-smoothness -/

/-- **Bridge lemma.**  For a positive natural number the spectrum predicate
`HasPositiveTwoThreeUnitPower` of `AlgebraicBaseUnitPower` is exactly three-smoothness.

One direction is immediate.  For the other, a positive natural power `M ^ n` equal to a
positive rational `2,3`-unit clears denominators to `M ^ n * (2 ^ k * 3 ^ l) = 2 ^ i * 3 ^ j`,
and unique factorization then confines every prime of `M` to `{2, 3}`.  This is the
kernel-verified counterpart of the report's remark that an *integer* lies in the saturated
group `{2 ^ r * 3 ^ s : r, s ∈ ℚ}` exactly when it is three-smooth. -/
theorem hasPositiveTwoThreeUnitPower_natCast_iff {M : ℕ} (hM : 0 < M) :
    HasPositiveTwoThreeUnitPower (M : ℝ) ↔ ∃ a b : ℕ, M = 2 ^ a * 3 ^ b := by
  constructor
  · rintro ⟨n, hn, q, _hqpos, ⟨i, j, k, l, hq⟩, hpow⟩
    have hqval : q = ((M ^ n : ℕ) : ℚ) := by
      have hreal : ((M ^ n : ℕ) : ℝ) = (q : ℝ) := by
        rw [Nat.cast_pow]
        exact hpow
      exact_mod_cast hreal.symm
    have hdenpos : (0 : ℚ) < ((2 ^ k * 3 ^ l : ℕ) : ℚ) := by
      have hpos : 0 < 2 ^ k * 3 ^ l := by positivity
      exact_mod_cast hpos
    have hmul : q * ((2 ^ k * 3 ^ l : ℕ) : ℚ) = ((2 ^ i * 3 ^ j : ℕ) : ℚ) :=
      (eq_div_iff hdenpos.ne').mp hq
    rw [hqval] at hmul
    have hnat : M ^ n * (2 ^ k * 3 ^ l) = 2 ^ i * 3 ^ j := by exact_mod_cast hmul
    rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hM]
    intro p hp hpM
    have hpdvd : p ∣ 2 ^ i * 3 ^ j := by
      rw [← hnat]
      exact dvd_mul_of_dvd_left (hpM.trans (dvd_pow_self M hn.ne')) _
    rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h3))
  · rintro ⟨a, b, rfl⟩
    have hqpos : (0 : ℚ) < ((2 ^ a * 3 ^ b : ℕ) : ℚ) := by exact_mod_cast hM
    have hunit : IsTwoThreeUnit ((2 ^ a * 3 ^ b : ℕ) : ℚ) := by
      refine ⟨a, b, 0, 0, ?_⟩
      norm_num
    refine ⟨1, Nat.one_pos, ((2 ^ a * 3 ^ b : ℕ) : ℚ), hqpos, hunit, ?_⟩
    rw [pow_one, Rat.cast_natCast]

/-! ### Level two of the base-two tower -/

/-- The second level of the base-two tower is the first output raised to `x`. -/
theorem two_rpow_mul_self_eq_output_rpow {x : ℝ} {M : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) :
    (2 : ℝ) ^ (x * x) = (M : ℝ) ^ x := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x x, hM]

/-- **The base-two second iterate in the three-smooth branch.**  If `M = 2 ^ x` and
`A = 3 ^ x` are natural numbers and `M = 2 ^ a * 3 ^ b`, then

`2 ^ (x * x) = M ^ x = (2 ^ x) ^ a * (3 ^ x) ^ b = M ^ a * A ^ b`,

an explicit natural number.  No nonintegrality hypothesis is used. -/
theorem two_rpow_mul_self_eq_of_threeSmooth_output {x : ℝ} {M A a b : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hsmooth : M = 2 ^ a * 3 ^ b) :
    (2 : ℝ) ^ (x * x) = ((M ^ a * A ^ b : ℕ) : ℝ) := by
  have hMreal : (M : ℝ) = (2 : ℝ) ^ a * (3 : ℝ) ^ b := by
    rw [hsmooth, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ (x * x) = (M : ℝ) ^ x := two_rpow_mul_self_eq_output_rpow hM
    _ = ((2 : ℝ) ^ a * (3 : ℝ) ^ b) ^ x := by rw [hMreal]
    _ = ((2 : ℝ) ^ a) ^ x * ((3 : ℝ) ^ b) ^ x :=
      Real.mul_rpow (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ x) ^ a * ((3 : ℝ) ^ x) ^ b := by
      rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x a,
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x b]
    _ = (M : ℝ) ^ a * (A : ℝ) ^ b := by rw [hM, hA]
    _ = ((M ^ a * A ^ b : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]

/-- In the three-smooth branch the second level of the base-two tower is a natural number. -/
theorem exists_nat_eq_two_rpow_mul_self_of_threeSmooth_output {x : ℝ} {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hsmooth : ∃ a b : ℕ, M = 2 ^ a * 3 ^ b) :
    ∃ N : ℕ, (N : ℝ) = (2 : ℝ) ^ (x * x) := by
  obtain ⟨a, b, hab⟩ := hsmooth
  exact ⟨M ^ a * A ^ b, (two_rpow_mul_self_eq_of_threeSmooth_output hM hA hab).symm⟩

/-- **The two outputs are not both three-smooth.**  Restatement of the smooth-output
exclusion for the two integral outputs of a nonintegral solution. -/
theorem TwoBaseNonintegerSolution.not_both_outputs_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x) :
    ¬ ((∃ a b : ℕ, M = 2 ^ a * 3 ^ b) ∧ ∃ c d : ℕ, A = 2 ^ c * 3 ^ d) := by
  rintro ⟨hMsmooth, hAsmooth⟩
  exact hx.2
    (integer_of_two_three_rpow_integer_of_threeSmooth_outputs hM hA hMsmooth hAsmooth)

/-- **Base-two depth-two dichotomy.**  For a nonintegral two-base solution with first output
`M = 2 ^ x`, the second tower level `2 ^ (x * x)` is algebraic exactly when `M` is
three-smooth. -/
theorem TwoBaseNonintegerSolution.two_rpow_mul_self_isAlgebraic_iff_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M : ℕ} (hMpos : 0 < M)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) :
    IsAlgebraic ℚ ((2 : ℝ) ^ (x * x)) ↔ ∃ a b : ℕ, M = 2 ^ a * 3 ^ b := by
  rw [two_rpow_mul_self_eq_output_rpow hM]
  calc
    IsAlgebraic ℚ ((M : ℝ) ^ x) ↔
        x ∈ Set.range ((↑) : ℤ → ℝ) ∨ ∃ a b : ℕ, M = 2 ^ a * 3 ^ b :=
      rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow hx.1.1 hx.1.2 hMpos
    _ ↔ ∃ a b : ℕ, M = 2 ^ a * 3 ^ b := by simp only [hx.2, false_or]

/-- The same dichotomy read through the algebraic-base spectrum theorem: the second tower
level is algebraic exactly when the first output has a positive rational `2,3`-unit power. -/
theorem TwoBaseNonintegerSolution.two_rpow_mul_self_isAlgebraic_iff_unitPower
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M : ℕ} (hMpos : 0 < M)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) :
    IsAlgebraic ℚ ((2 : ℝ) ^ (x * x)) ↔ HasPositiveTwoThreeUnitPower (M : ℝ) :=
  (hx.two_rpow_mul_self_isAlgebraic_iff_threeSmooth hMpos hM).trans
    (hasPositiveTwoThreeUnitPower_natCast_iff hMpos).symm

/-- Depth two, transcendence form: a first output with an external prime factor makes the
second level of the base-two tower transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_two_rpow_mul_self_of_not_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M : ℕ} (hMpos : 0 < M)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hns : ¬ ∃ a b : ℕ, M = 2 ^ a * 3 ^ b) :
    Transcendental ℚ ((2 : ℝ) ^ (x * x)) := by
  intro halg
  exact hns ((hx.two_rpow_mul_self_isAlgebraic_iff_threeSmooth hMpos hM).mp halg)

/-! ### Level three of the base-two tower -/

/-- **The third level has nowhere to land.**  If the first output of a nonintegral solution is
three-smooth, `M = 2 ^ a * 3 ^ b`, then the second-level value `M ^ a * A ^ b` is not
three-smooth.

Two facts combine.  First `b ≠ 0`: otherwise `M = 2 ^ a` and comparing logarithms forces
`x = a`, an integer.  Second, with `M` three-smooth the partner output `A` must carry a prime
factor at least `5`, and that prime divides `A ^ b` and hence `M ^ a * A ^ b`. -/
private theorem not_threeSmooth_second_level {x : ℝ} {M A a b : ℕ}
    (hMpos : 0 < M) (hApos : 0 < A)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hxint : x ∉ Set.range ((↑) : ℤ → ℝ))
    (hab : M = 2 ^ a * 3 ^ b) :
    ¬ ∃ u v : ℕ, M ^ a * A ^ b = 2 ^ u * 3 ^ v := by
  have hb : b ≠ 0 := by
    intro hb0
    apply hxint
    refine ⟨(a : ℤ), ?_⟩
    have hMa : M = 2 ^ a := by rw [hab, hb0, pow_zero, mul_one]
    have hcast : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ x := by
      rw [← hMa]
      exact hM
    have hxa : x = (a : ℝ) := eq_natCast_of_two_rpow_eq_two_pow hcast
    push_cast
    exact hxa.symm
  obtain ⟨p, hp, hp5, hpA⟩ :=
    exists_prime_five_le_dvd_of_threeSmooth_candidate hM hA hxint ⟨a, b, hab⟩
  rintro ⟨u, v, huv⟩
  have hNpos : 0 < M ^ a * A ^ b := mul_pos (pow_pos hMpos a) (pow_pos hApos b)
  have hpN : p ∣ M ^ a * A ^ b :=
    dvd_mul_of_dvd_right (hpA.trans (dvd_pow_self A hb)) _
  have hp23 : p = 2 ∨ p = 3 :=
    (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hNpos).mpr
      ⟨u, v, huv⟩ p hp hpN
  rcases hp23 with h | h <;> omega

/-- **Base-two depth three.**  In the three-smooth branch the second level of the base-two
tower is a natural number, and the third level `2 ^ (x * x * x)` is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_two_rpow_cube_of_threeSmooth
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M A : ℕ}
    (hMpos : 0 < M) (hApos : 0 < A)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hsmooth : ∃ a b : ℕ, M = 2 ^ a * 3 ^ b) :
    Transcendental ℚ ((2 : ℝ) ^ (x * x * x)) := by
  obtain ⟨a, b, hab⟩ := hsmooth
  have hNpos : 0 < M ^ a * A ^ b := mul_pos (pow_pos hMpos a) (pow_pos hApos b)
  have hNval : ((M ^ a * A ^ b : ℕ) : ℝ) = (2 : ℝ) ^ (x * x) :=
    (two_rpow_mul_self_eq_of_threeSmooth_output hM hA hab).symm
  have hcube : (2 : ℝ) ^ (x * x * x) = ((M ^ a * A ^ b : ℕ) : ℝ) ^ x := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (x * x) x, hNval]
  intro halg
  rw [hcube] at halg
  rcases (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
      hx.1.1 hx.1.2 hNpos).mp halg with hxint | hNsmooth
  · exact hx.2 hxint
  · exact not_threeSmooth_second_level hMpos hApos hM hA hx.2 hab hNsmooth

/-- **Base-two tower dichotomy.**  For a nonintegral two-base solution exactly one of two
things happens.  Either the first output `M = 2 ^ x` is not three-smooth and the second tower
level is already transcendental, or `M` is three-smooth, the second level is a natural number,
and the third level is transcendental. -/
theorem TwoBaseNonintegerSolution.base_two_tower_dichotomy
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M A : ℕ}
    (hMpos : 0 < M) (hApos : 0 < A)
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x) :
    (¬ (∃ a b : ℕ, M = 2 ^ a * 3 ^ b) ∧ Transcendental ℚ ((2 : ℝ) ^ (x * x))) ∨
      ((∃ a b : ℕ, M = 2 ^ a * 3 ^ b) ∧
        (∃ N : ℕ, (N : ℝ) = (2 : ℝ) ^ (x * x)) ∧
          Transcendental ℚ ((2 : ℝ) ^ (x * x * x))) := by
  by_cases hsmooth : ∃ a b : ℕ, M = 2 ^ a * 3 ^ b
  · exact Or.inr ⟨hsmooth,
      exists_nat_eq_two_rpow_mul_self_of_threeSmooth_output hM hA hsmooth,
      hx.transcendental_two_rpow_cube_of_threeSmooth hMpos hApos hM hA hsmooth⟩
  · exact Or.inl ⟨hsmooth,
      hx.transcendental_two_rpow_mul_self_of_not_threeSmooth hMpos hM hsmooth⟩

/-! ### The base-two three-level detector -/

/-- **Base-two cubic-tower equivalence.**  The Alaoglu--Erdős conjecture is equivalent to the
assertion that both `2 ^ (x * x)` and `2 ^ (x * x * x)` are algebraic at every two-base
integral-power solution.

The forward direction is immediate, since a counterexample-free world makes `x`, `x ^ 2` and
`x ^ 3` integers.  The reverse direction is the tower dichotomy: a nonintegral solution whose
first output is not three-smooth already fails at level two, and one whose first output is
three-smooth fails at level three. -/
theorem alaogluErdosConjecture_iff_two_rpow_square_cube_isAlgebraic :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        IsAlgebraic ℚ ((2 : ℝ) ^ (x * x)) ∧
          IsAlgebraic ℚ ((2 : ℝ) ^ (x * x * x)) := by
  constructor
  · intro hAE x hx
    have halgTwo : IsAlgebraic ℚ (2 : ℝ) := isAlgebraic_nat 2
    have hxint : x ∈ Set.range ((↑) : ℤ → ℝ) := hAE hx.1 hx.2
    have hsq : x * x ∈ Set.range ((↑) : ℤ → ℝ) := mul_mem_range_intCast hxint hxint
    exact ⟨algebraic_rpow_of_integer_exponent halgTwo hsq,
      algebraic_rpow_of_integer_exponent halgTwo (mul_mem_range_intCast hsq hxint)⟩
  · intro htower x h₂ h₃
    by_contra hxint
    have hx : TwoBaseNonintegerSolution x := ⟨⟨h₂, h₃⟩, hxint⟩
    obtain ⟨M, hMpos, hM⟩ := exists_pos_nat_eq_rpow (by norm_num : (0 : ℝ) < 2) h₂
    obtain ⟨A, hApos, hA⟩ := exists_pos_nat_eq_rpow (by norm_num : (0 : ℝ) < 3) h₃
    by_cases hsmooth : ∃ a b : ℕ, M = 2 ^ a * 3 ^ b
    · exact hx.transcendental_two_rpow_cube_of_threeSmooth hMpos hApos hM hA hsmooth
        (htower ⟨h₂, h₃⟩).2
    · exact hx.transcendental_two_rpow_mul_self_of_not_threeSmooth hMpos hM hsmooth
        (htower ⟨h₂, h₃⟩).1

/-- The base-two three-level detector written with the exponents `x ^ 2` and `x ^ 3`. -/
theorem alaogluErdosConjecture_iff_two_rpow_pow_two_pow_three_isAlgebraic :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        IsAlgebraic ℚ ((2 : ℝ) ^ (x ^ 2)) ∧
          IsAlgebraic ℚ ((2 : ℝ) ^ (x ^ 3)) := by
  constructor
  · intro hAE x hx
    have h := alaogluErdosConjecture_iff_two_rpow_square_cube_isAlgebraic.mp hAE hx
    rw [pow_two, pow_three']
    exact h
  · intro htower
    refine alaogluErdosConjecture_iff_two_rpow_square_cube_isAlgebraic.mpr ?_
    intro x hx
    have h := htower hx
    rw [pow_two, pow_three'] at h
    exact h

end

end LeanProofs.TwoBaseIntegerExponent
