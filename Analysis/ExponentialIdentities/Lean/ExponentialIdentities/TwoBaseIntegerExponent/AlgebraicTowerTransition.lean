import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicBaseUnitPower
import ExponentialIdentities.TwoBaseIntegerExponent.Transcendence
import ExponentialIdentities.TwoBaseIntegerExponent.RationalFunctionRigidity

/-!
# Algebraic transitions in the base-two power tower

For a hypothetical nonintegral two-base solution `x`, this file classifies the
exponents `y` for which both `2^y` and `2^(y*x)` are algebraic.  They are exactly
the rational affine span of `1` and `log 3 / log 2`.

The classification makes the tower restriction global: no two distinct
positive depths can both begin an adjacent pair of algebraic base-two tower
levels.  Thus every finite set of depths contains at most one such transition.
Requiring transitions at any two fixed distinct positive depths is consequently
equivalent to the Alaoglu--Erdős conjecture.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

private theorem two_rpow_logThreeDivLogTwo :
    (2 : ℝ) ^ logThreeDivLogTwo = 3 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logThreeDivLogTwo]
  have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
      Real.log (3 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

private theorem log_three_eq_log_two_mul :
    Real.log 3 = Real.log 2 * logThreeDivLogTwo := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [logThreeDivLogTwo, mul_comm (Real.log 2) (Real.log 3 / Real.log 2),
    div_mul_cancel₀ _ hlog2]

private theorem isTwoThreeUnit_zpow_mul_zpow (a b : ℤ) :
    IsTwoThreeUnit ((2 : ℚ) ^ a * (3 : ℚ) ^ b) := by
  cases a with
  | ofNat i =>
      cases b with
      | ofNat j =>
          refine ⟨i, j, 0, 0, ?_⟩
          norm_num
      | negSucc j =>
          refine ⟨i, 0, 0, j + 1, ?_⟩
          norm_num [zpow_negSucc]
          rw [div_eq_mul_inv]
  | negSucc i =>
      cases b with
      | ofNat j =>
          refine ⟨0, j, i + 1, 0, ?_⟩
          norm_num [zpow_negSucc]
          rw [div_eq_mul_inv]
          ring
      | negSucc j =>
          refine ⟨0, 0, i + 1, j + 1, ?_⟩
          norm_num [zpow_negSucc]
          ring

/-- A power of two has a positive rational `2,3`-unit power exactly when its
exponent lies in the rational affine span of `1` and `log 3 / log 2`. -/
theorem hasPositiveTwoThreeUnitPower_two_rpow_iff_affine_logRatio {y : ℝ} :
    HasPositiveTwoThreeUnitPower ((2 : ℝ) ^ y) ↔
      ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * logThreeDivLogTwo := by
  constructor
  · rintro ⟨n, hn, q, _hqpos, ⟨i, j, k, l, hq⟩, hpow⟩
    have hqcast := congrArg (fun z : ℚ ↦ (z : ℝ)) hq
    norm_num only [Rat.cast_div, Rat.cast_natCast, Nat.cast_mul, Nat.cast_pow] at hqcast
    have hlog := congrArg Real.log hpow
    rw [Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 2), hqcast,
      Real.log_div (by positivity) (by positivity)] at hlog
    push_cast at hlog
    rw [
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
      log_three_eq_log_two_mul] at hlog
    refine ⟨((((i : ℤ) - (k : ℤ) : ℤ) : ℚ) / n),
      ((((j : ℤ) - (l : ℤ) : ℤ) : ℚ) / n), ?_⟩
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have hscaled :
        (n : ℝ) * y = ((i : ℝ) - (k : ℝ)) +
          ((j : ℝ) - (l : ℝ)) * logThreeDivLogTwo := by
      apply mul_left_cancel₀ hlog2
      linear_combination hlog
    push_cast
    field_simp
    linear_combination hscaled
  · rintro ⟨q, r, rfl⟩
    let n : ℕ := q.den * r.den
    let a : ℤ := q.num * r.den
    let b : ℤ := r.num * q.den
    have hn : 0 < n := mul_pos q.den_pos r.den_pos
    let u : ℚ := (2 : ℚ) ^ a * (3 : ℚ) ^ b
    have huPos : 0 < u := by
      dsimp only [u]
      positivity
    have huUnit : IsTwoThreeUnit u := isTwoThreeUnit_zpow_mul_zpow a b
    refine ⟨n, hn, u, huPos, huUnit, ?_⟩
    have hscaled :
        ((q : ℝ) + (r : ℝ) * logThreeDivLogTwo) * (n : ℝ) =
          (a : ℝ) + (b : ℝ) * logThreeDivLogTwo := by
      dsimp only [n, a, b]
      rw [Rat.cast_def, Rat.cast_def]
      push_cast
      field_simp
    calc
      ((2 : ℝ) ^ ((q : ℝ) + (r : ℝ) * logThreeDivLogTwo)) ^ n =
          (2 : ℝ) ^ (((q : ℝ) + (r : ℝ) * logThreeDivLogTwo) * (n : ℝ)) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((a : ℝ) + (b : ℝ) * logThreeDivLogTwo) := by rw [hscaled]
      _ = (2 : ℝ) ^ (a : ℝ) *
          (2 : ℝ) ^ ((b : ℝ) * logThreeDivLogTwo) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = (2 : ℝ) ^ (a : ℝ) *
          (((2 : ℝ) ^ logThreeDivLogTwo) ^ (b : ℝ)) := by
            rw [mul_comm (b : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ a * (3 : ℝ) ^ b := by
            rw [two_rpow_logThreeDivLogTwo, Real.rpow_intCast, Real.rpow_intCast]
      _ = (u : ℝ) := by
            dsimp only [u]
            push_cast
            rfl

/-- The base-two algebraic transition predicate: both the value at exponent `y`
and its next `x`-iterate are algebraic. -/
def TwoRpowAlgebraicTransition (x y : ℝ) : Prop :=
  IsAlgebraic ℚ ((2 : ℝ) ^ y) ∧ IsAlgebraic ℚ ((2 : ℝ) ^ (y * x))

/-- Exact transition locus under a hypothetical nonintegral two-base solution.
The answer is independent of the solution `x`: it is `ℚ + ℚ * logThreeDivLogTwo`. -/
theorem TwoBaseNonintegerSolution.twoRpowAlgebraicTransition_iff_affine_logRatio
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {y : ℝ} :
    TwoRpowAlgebraicTransition x y ↔
      ∃ q r : ℚ, y = (q : ℝ) + (r : ℝ) * logThreeDivLogTwo := by
  rw [← hasPositiveTwoThreeUnitPower_two_rpow_iff_affine_logRatio]
  constructor
  · rintro ⟨hyAlg, hyxAlg⟩
    apply (hx.real_rpow_isAlgebraic_iff_hasPositiveTwoThreeUnitPower
      (Real.rpow_pos_of_pos (by norm_num) y) hyAlg).mp
    simpa only [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] using hyxAlg
  · intro hunit
    have hyAlg : IsAlgebraic ℚ ((2 : ℝ) ^ y) := by
      obtain ⟨n, hn, q, _hqpos, _hunit, hpow⟩ := hunit
      apply IsAlgebraic.of_pow hn
      rw [hpow]
      exact isAlgebraic_rat ℚ q
    refine ⟨hyAlg, ?_⟩
    have hnext := (hx.real_rpow_isAlgebraic_iff_hasPositiveTwoThreeUnitPower
      (Real.rpow_pos_of_pos (by norm_num) y) hyAlg).mpr hunit
    simpa only [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] using hnext

private theorem not_consecutive_powers_both_affine_logRatio
    {x : ℝ} (hxTrans : Transcendental ℚ x) {n : ℕ} (hn : 0 < n) :
    ¬ ((∃ q r : ℚ,
          x ^ n = (q : ℝ) + (r : ℝ) * logThreeDivLogTwo) ∧
        ∃ s t : ℚ,
          x ^ (n + 1) = (s : ℝ) + (t : ℝ) * logThreeDivLogTwo) := by
  rintro ⟨⟨q, r, h₁⟩, ⟨s, t, h₂⟩⟩
  by_cases hr : r = 0
  · subst r
    apply hxTrans
    apply IsAlgebraic.of_pow hn
    rw [h₁]
    simp only [Rat.cast_zero, zero_mul, add_zero]
    exact isAlgebraic_rat ℚ q
  · have hrel :
        (r : ℝ) * x ^ (n + 1) - (t : ℝ) * x ^ n +
            ((t : ℝ) * (q : ℝ) - (r : ℝ) * (s : ℝ)) = 0 := by
      linear_combination (r : ℝ) * h₂ - (t : ℝ) * h₁
    apply hxTrans
    let P : Polynomial ℚ :=
      Polynomial.C r * Polynomial.X ^ (n + 1) -
        Polynomial.C t * Polynomial.X ^ n + Polynomial.C (t * q - r * s)
    refine ⟨P, ?_, ?_⟩
    · intro hzero
      have hcoeff := congrArg (fun f : Polynomial ℚ ↦ f.coeff (n + 1)) hzero
      have hne : n ≠ n + 1 := Nat.ne_add_one n
      have hpos : n + 1 ≠ 0 := by omega
      simp [P, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hcoeff
      exact hr hcoeff
    · simp only [P, map_add, map_sub, map_mul, map_pow,
        Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
      exact hrel

/-- In a hypothetical counterexample, no three consecutive levels of the
base-two power tower can all be algebraic.  This holds at every depth `n ≥ 1`,
not only for the square/cube pair at the bottom of the tower. -/
theorem TwoBaseNonintegerSolution.not_three_consecutive_two_rpow_tower_algebraic
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n : ℕ} (hn : 0 < n) :
    ¬ (IsAlgebraic ℚ ((2 : ℝ) ^ (x ^ n)) ∧
        IsAlgebraic ℚ ((2 : ℝ) ^ (x ^ (n + 1))) ∧
        IsAlgebraic ℚ ((2 : ℝ) ^ (x ^ (n + 2)))) := by
  rintro ⟨h₀, h₁, h₂⟩
  have ht₀ : TwoRpowAlgebraicTransition x (x ^ n) := by
    refine ⟨h₀, ?_⟩
    simpa only [pow_succ] using h₁
  have ht₁ : TwoRpowAlgebraicTransition x (x ^ (n + 1)) := by
    refine ⟨h₁, ?_⟩
    have heq : n + 2 = (n + 1) + 1 := by omega
    rw [heq, pow_succ] at h₂
    exact h₂
  exact not_consecutive_powers_both_affine_logRatio
    (transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2) hn
    ⟨(hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp ht₀,
      (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp ht₁⟩

/-- Transcendence form of the all-depth tower restriction: every three
consecutive positive-depth base-two tower levels contain a transcendental one. -/
theorem TwoBaseNonintegerSolution.transcendental_one_of_three_consecutive_two_rpow_tower
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n : ℕ} (hn : 0 < n) :
    Transcendental ℚ ((2 : ℝ) ^ (x ^ n)) ∨
      Transcendental ℚ ((2 : ℝ) ^ (x ^ (n + 1))) ∨
      Transcendental ℚ ((2 : ℝ) ^ (x ^ (n + 2))) := by
  have h := hx.not_three_consecutive_two_rpow_tower_algebraic hn
  tauto

/-! ### Global uniqueness of an algebraic transition depth -/

/-- Two distinct positive depths cannot both have an algebraic adjacent pair in
the base-two tower of a hypothetical nonintegral solution. -/
theorem TwoBaseNonintegerSolution.not_two_distinct_algebraic_tower_transitions
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) :
    ¬ (TwoRpowAlgebraicTransition x (x ^ n) ∧
        TwoRpowAlgebraicTransition x (x ^ m)) := by
  rintro ⟨htransN, htransM⟩
  obtain ⟨a, b, hN⟩ :=
    (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp htransN
  obtain ⟨c, d, hM⟩ :=
    (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp htransM
  have hxTrans : Transcendental ℚ x :=
    transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2
  have hb : b ≠ 0 := by
    intro hb0
    subst b
    apply hxTrans
    apply IsAlgebraic.of_pow hn
    rw [hN]
    simp only [Rat.cast_zero, zero_mul, add_zero]
    exact isAlgebraic_rat ℚ a
  have hd : d ≠ 0 := by
    intro hd0
    subst d
    apply hxTrans
    apply IsAlgebraic.of_pow hm
    rw [hM]
    simp only [Rat.cast_zero, zero_mul, add_zero]
    exact isAlgebraic_rat ℚ c
  let P : Polynomial ℚ :=
    Polynomial.C b * Polynomial.X + Polynomial.C a
  let Q : Polynomial ℚ :=
    Polynomial.C d * Polynomial.X + Polynomial.C c
  have hPeval : Polynomial.aeval logThreeDivLogTwo P = x ^ n := by
    dsimp only [P]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    linear_combination -hN
  have hQeval : Polynomial.aeval logThreeDivLogTwo Q = x ^ m := by
    dsimp only [Q]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    linear_combination -hM
  have hpowEval :
      Polynomial.aeval logThreeDivLogTwo (P ^ m) =
        Polynomial.aeval logThreeDivLogTwo (Q ^ n) := by
    calc
      Polynomial.aeval logThreeDivLogTwo (P ^ m) =
          (Polynomial.aeval logThreeDivLogTwo P) ^ m := by rw [map_pow]
      _ = (x ^ n) ^ m := by rw [hPeval]
      _ = x ^ (n * m) := (pow_mul x n m).symm
      _ = x ^ (m * n) := by rw [Nat.mul_comm n m]
      _ = (x ^ m) ^ n := pow_mul x m n
      _ = (Polynomial.aeval logThreeDivLogTwo Q) ^ n := by rw [hQeval]
      _ = Polynomial.aeval logThreeDivLogTwo (Q ^ n) := by rw [map_pow]
  have hpoly : P ^ m = Q ^ n :=
    eq_of_aeval_eq_of_transcendental transcendental_logThreeDivLogTwo hpowEval
  have hdegree := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    show P.natDegree = 1 by exact Polynomial.natDegree_linear hb,
    show Q.natDegree = 1 by exact Polynomial.natDegree_linear hd,
    Nat.mul_one, Nat.mul_one] at hdegree
  exact hnm hdegree.symm

/-- Positive depths from a finite search range at which an algebraic adjacent
tower pair occurs. -/
def algebraicTowerTransitionDepths (x : ℝ) (s : Finset ℕ) : Finset ℕ :=
  by
    classical
    exact s.filter fun n ↦ 0 < n ∧ TwoRpowAlgebraicTransition x (x ^ n)

/-- Every finite set contains at most one positive algebraic transition depth. -/
theorem TwoBaseNonintegerSolution.card_algebraicTowerTransitionDepths_le_one
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) (s : Finset ℕ) :
    (algebraicTowerTransitionDepths x s).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro n hn m hm
  simp only [algebraicTowerTransitionDepths, Finset.mem_filter] at hn hm
  by_contra hnm
  exact hx.not_two_distinct_algebraic_tower_transitions
    hn.2.1 hm.2.1 hnm ⟨hn.2.2, hm.2.2⟩

/-! ### A fixed-depth global equivalence -/

private theorem isAlgebraic_two_rpow_intCast (z : ℤ) :
    IsAlgebraic ℚ ((2 : ℝ) ^ (z : ℝ)) := by
  rw [Real.rpow_intCast]
  have hcast : (2 : ℝ) ^ z = (((2 : ℚ) ^ z : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  exact isAlgebraic_rat ℚ ((2 : ℚ) ^ z)

private theorem twoRpowAlgebraicTransition_of_integer
    {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (n : ℕ) :
    TwoRpowAlgebraicTransition x (x ^ n) := by
  obtain ⟨z, rfl⟩ := hx
  constructor
  · convert isAlgebraic_two_rpow_intCast (z ^ n) using 1
    push_cast
    rfl
  · convert isAlgebraic_two_rpow_intCast (z ^ n * z) using 1
    push_cast
    rfl

/-- For any two distinct positive depths, Alaoglu--Erdős is equivalent to every
two-base integral solution having algebraic adjacent base-two tower pairs at
both depths. -/
theorem alaogluErdosConjecture_iff_two_distinct_tower_transitions_algebraic
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        TwoRpowAlgebraicTransition x (x ^ n) ∧
          TwoRpowAlgebraicTransition x (x ^ m) := by
  constructor
  · intro hAE x hx
    have hxint : x ∈ Set.range ((↑) : ℤ → ℝ) := hAE hx.1 hx.2
    exact ⟨twoRpowAlgebraicTransition_of_integer hxint n,
      twoRpowAlgebraicTransition_of_integer hxint m⟩
  · intro htransitions x h₂ h₃
    by_contra hxint
    have hx : TwoBaseNonintegerSolution x := ⟨⟨h₂, h₃⟩, hxint⟩
    exact hx.not_two_distinct_algebraic_tower_transitions hn hm hnm
      (htransitions ⟨h₂, h₃⟩)

end

end LeanProofs.TwoBaseIntegerExponent
