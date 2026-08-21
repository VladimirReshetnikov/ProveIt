import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Localized-radical reformulation of the Alaoglu--Erdős conjecture

Every positive natural number is a power of two times an odd number.  Applying this
decomposition to the candidate value `m = 2 ^ x` shows that a counterexample to the
Alaoglu--Erdős conjecture is equivalent to an integral value of a localized irrational
power

`3 ^ a * u ^ (log 3 / log 2)`

with an odd integer `u > 1`.  The strict inequality removes exactly the ordinary integral
exponents, whose candidate values are powers of two.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The exponent obtained by interchanging the bases two and three. -/
def logTwoDivLogThree : ℝ := Real.log 2 / Real.log 3

private theorem two_rpow_logThreeDivLogTwo :
    (2 : ℝ) ^ logThreeDivLogTwo = 3 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logThreeDivLogTwo]
  have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
      Real.log (3 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

private theorem two_pow_mul_rpow_logThreeDivLogTwo (a u : ℕ) :
    (((2 ^ a * u : ℕ) : ℝ) ^ logThreeDivLogTwo) =
      (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity)]
  norm_num only [Nat.cast_ofNat]
  rw [
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) logThreeDivLogTwo a,
    two_rpow_logThreeDivLogTwo]

private theorem three_rpow_logTwoDivLogThree :
    (3 : ℝ) ^ logTwoDivLogThree = 2 := by
  have hlog3 : Real.log (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), logTwoDivLogThree]
  have hmul : Real.log (3 : ℝ) * (Real.log (2 : ℝ) / Real.log (3 : ℝ)) =
      Real.log (2 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem three_pow_mul_rpow_logTwoDivLogThree (b v : ℕ) :
    (((3 ^ b * v : ℕ) : ℝ) ^ logTwoDivLogThree) =
      (2 : ℝ) ^ b * (v : ℝ) ^ logTwoDivLogThree := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity)]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) logTwoDivLogThree b,
    three_rpow_logTwoDivLogThree]

private theorem three_rpow_rpow_logTwoDivLogThree (x : ℝ) :
    ((3 : ℝ) ^ x) ^ logTwoDivLogThree = (2 : ℝ) ^ x := by
  have hlog3 : Real.log (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logTwoDivLogThree]
  congr 1
  field_simp

private theorem two_rpow_logb_three_eq_rpow_logTwoDivLogThree
    {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) ^ Real.logb 3 n = (n : ℝ) ^ logTwoDivLogThree := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by exact_mod_cast hn), Real.logb, logTwoDivLogThree]
  congr 1
  ring

/-- Failure of the Alaoglu--Erdős conjecture is equivalent to the existence of an odd
`u > 1` whose `log 3 / log 2` power becomes integral after multiplication by a power of
three. -/
theorem not_alaogluErdosConjecture_iff_exists_odd_localized_radical :
    ¬ AlaogluErdosConjecture ↔
      ∃ u a B : ℕ, Odd u ∧ 1 < u ∧
        (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo = (B : ℝ) := by
  classical
  constructor
  · intro hfail
    rw [alaogluErdosConjecture_iff_candidates_are_powers_of_two] at hfail
    push Not at hfail
    obtain ⟨m, hm, hmNotPow⟩ := hfail
    obtain ⟨a, u, huOdd, hmEq⟩ := Nat.exists_eq_two_pow_mul_odd hm.1.ne'
    have huPos : 0 < u := huOdd.pos
    have huNeOne : u ≠ 1 := by
      intro hu
      apply hmNotPow a
      rw [hmEq, hu, mul_one]
    have huOne : 1 < u := by omega
    obtain ⟨z, hz⟩ := hm.2
    have hzPosR : (0 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact Real.rpow_pos_of_pos (by exact_mod_cast hm.1) _
    have hzPos : (0 : ℤ) < z := by exact_mod_cast hzPosR
    obtain ⟨B, rfl⟩ := Int.eq_ofNat_of_zero_le hzPos.le
    refine ⟨u, a, B, huOdd, huOne, ?_⟩
    calc
      (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo =
          (((2 ^ a * u : ℕ) : ℝ) ^ logThreeDivLogTwo) :=
        (two_pow_mul_rpow_logThreeDivLogTwo a u).symm
      _ = (m : ℝ) ^ logThreeDivLogTwo := by rw [hmEq]
      _ = (B : ℝ) := by exact_mod_cast hz.symm
  · rintro ⟨u, a, B, huOdd, huOne, hrad⟩ hconj
    let m : ℕ := 2 ^ a * u
    have hmPos : 0 < m := by
      dsimp only [m]
      positivity
    have hmCandidate : TwoBaseNaturalCandidate m := by
      refine ⟨hmPos, ⟨(B : ℤ), ?_⟩⟩
      change (B : ℝ) = (m : ℝ) ^ logThreeDivLogTwo
      calc
        (B : ℝ) = (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo := hrad.symm
        _ = (m : ℝ) ^ logThreeDivLogTwo := by
          exact (two_pow_mul_rpow_logThreeDivLogTwo a u).symm
    have hmNotPow : ¬ ∃ n : ℕ, m = 2 ^ n := by
      rintro ⟨n, hn⟩
      have hc := congrArg (fun t : ℕ ↦ ordCompl[2] t) hn
      change ordCompl[2] (2 ^ a * u) = ordCompl[2] (2 ^ n) at hc
      rw [Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two huOdd.not_two_dvd_nat,
        Nat.ordCompl_self_pow Nat.prime_two] at hc
      omega
    exact hmNotPow
      ((alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp hconj) m hmCandidate)

/-- Positive formulation of the remaining localized-radical obstruction: no odd `u > 1`
may acquire an integral `log 3 / log 2` power after clearing a power of three. -/
def OddLocalizedRadicalExclusion : Prop :=
  ∀ u a B : ℕ, Odd u → 1 < u →
    (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo ≠ (B : ℝ)

/-- The Alaoglu--Erdős conjecture is exactly the odd localized-radical exclusion, with no
loss in either direction. -/
theorem alaogluErdosConjecture_iff_oddLocalizedRadicalExclusion :
    AlaogluErdosConjecture ↔ OddLocalizedRadicalExclusion := by
  constructor
  · intro hconj u a B huodd hu1 heq
    have hfail :=
      not_alaogluErdosConjecture_iff_exists_odd_localized_radical.mpr
        ⟨u, a, B, huodd, hu1, heq⟩
    exact hfail hconj
  · intro hexcl
    by_contra hfail
    obtain ⟨u, a, B, huodd, hu1, heq⟩ :=
      not_alaogluErdosConjecture_iff_exists_odd_localized_radical.mp hfail
    exact hexcl u a B huodd hu1 heq

/-- Swapping the roles of two and three gives a symmetric localized-radical formulation.
Here `v` is the part of the integral value `3 ^ x` not divisible by three. -/
theorem not_alaogluErdosConjecture_iff_exists_threeFree_localized_radical :
    ¬ AlaogluErdosConjecture ↔
      ∃ v b A : ℕ, ¬ 3 ∣ v ∧ 1 < v ∧
        (2 : ℝ) ^ b * (v : ℝ) ^ logTwoDivLogThree = (A : ℝ) := by
  classical
  constructor
  · intro hfail
    change ¬ ∀ {x : ℝ},
      (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
      (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
      x ∈ Set.range ((↑) : ℤ → ℝ) at hfail
    push Not at hfail
    obtain ⟨x, hxTwo, hxThree, hxNotInt⟩ := hfail
    obtain ⟨zA, hzA⟩ := hxTwo
    have hzAPosR : (0 : ℝ) < (zA : ℝ) := by
      rw [hzA]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
    have hzAPos : (0 : ℤ) < zA := by exact_mod_cast hzAPosR
    obtain ⟨A, rfl⟩ := Int.eq_ofNat_of_zero_le hzAPos.le
    have hzA' : (A : ℝ) = (2 : ℝ) ^ x := by exact_mod_cast hzA
    obtain ⟨zN, hzN⟩ := hxThree
    have hzNPosR : (0 : ℝ) < (zN : ℝ) := by
      rw [hzN]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hzNPos : (0 : ℤ) < zN := by exact_mod_cast hzNPosR
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hzNPos.le
    have hzN' : (n : ℝ) = (3 : ℝ) ^ x := by exact_mod_cast hzN
    have hnPos : 0 < n := by exact_mod_cast hzNPos
    obtain ⟨b, v, hvThree, hnEq⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hnPos.ne' 3 (by norm_num)
    have hvPos : 0 < v := by
      rw [hnEq] at hnPos
      by_contra hv
      have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv
      simp [hv0] at hnPos
    have hvNeOne : v ≠ 1 := by
      intro hvOne
      apply hxNotInt
      refine ⟨(b : ℤ), ?_⟩
      change (b : ℝ) = x
      apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 3)).injective
      calc
        (3 : ℝ) ^ (b : ℝ) = ((3 ^ b : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]
          norm_cast
        _ = (n : ℝ) := by rw [hnEq, hvOne, mul_one]
        _ = (3 : ℝ) ^ x := hzN'
    have hvOne : 1 < v := by omega
    refine ⟨v, b, A, hvThree, hvOne, ?_⟩
    calc
      (2 : ℝ) ^ b * (v : ℝ) ^ logTwoDivLogThree =
          (((3 ^ b * v : ℕ) : ℝ) ^ logTwoDivLogThree) :=
        (three_pow_mul_rpow_logTwoDivLogThree b v).symm
      _ = (n : ℝ) ^ logTwoDivLogThree := by rw [hnEq]
      _ = ((3 : ℝ) ^ x) ^ logTwoDivLogThree := by rw [← hzN']
      _ = (2 : ℝ) ^ x := three_rpow_rpow_logTwoDivLogThree x
      _ = (A : ℝ) := hzA'.symm
  · rintro ⟨v, b, A, hvThree, hvOne, hrad⟩ hconj
    let n : ℕ := 3 ^ b * v
    let x : ℝ := Real.logb 3 n
    have hnPos : 0 < n := by
      dsimp only [n]
      positivity
    have hxThree : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨(n : ℤ), ?_⟩
      change (n : ℝ) = (3 : ℝ) ^ x
      exact (Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hnPos)).symm
    have hxTwo : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨(A : ℤ), ?_⟩
      change (A : ℝ) = (2 : ℝ) ^ x
      calc
        (A : ℝ) = (2 : ℝ) ^ b * (v : ℝ) ^ logTwoDivLogThree := hrad.symm
        _ = (n : ℝ) ^ logTwoDivLogThree :=
          (three_pow_mul_rpow_logTwoDivLogThree b v).symm
        _ = (2 : ℝ) ^ x :=
          (two_rpow_logb_three_eq_rpow_logTwoDivLogThree hnPos).symm
    obtain ⟨z, hz⟩ := hconj hxTwo hxThree
    have hxNonneg : 0 ≤ x := by
      dsimp only [x]
      exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) (by exact_mod_cast hnPos)
    have hzNonnegR : (0 : ℝ) ≤ (z : ℝ) := by rw [hz]; exact hxNonneg
    have hzNonneg : (0 : ℤ) ≤ z := by exact_mod_cast hzNonnegR
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hzNonneg
    have hz' : (k : ℝ) = x := by exact_mod_cast hz
    have hnPow : n = 3 ^ k := by
      have hpowR : (n : ℝ) = ((3 ^ k : ℕ) : ℝ) := by
        calc
          (n : ℝ) = (3 : ℝ) ^ x :=
            (Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hnPos)).symm
          _ = (3 : ℝ) ^ (k : ℝ) := by rw [hz']
          _ = ((3 ^ k : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
      exact_mod_cast hpowR
    have hc := congrArg (fun t : ℕ ↦ ordCompl[3] t) hnPow
    change ordCompl[3] (3 ^ b * v) = ordCompl[3] (3 ^ k) at hc
    rw [Nat.ordCompl_pow_mul_of_not_dvd b Nat.prime_three hvThree,
      Nat.ordCompl_self_pow Nat.prime_three] at hc
    omega

/-- Symmetric base-swapped exclusion at the prime two. -/
def ThreeFreeLocalizedRadicalExclusion : Prop :=
  ∀ v b A : ℕ, ¬ 3 ∣ v → 1 < v →
    (2 : ℝ) ^ b * (v : ℝ) ^ logTwoDivLogThree ≠ (A : ℝ)

/-- Symmetric positive reformulation obtained by exchanging bases two and three. -/
theorem alaogluErdosConjecture_iff_threeFreeLocalizedRadicalExclusion :
    AlaogluErdosConjecture ↔ ThreeFreeLocalizedRadicalExclusion := by
  constructor
  · intro hconj v b A hv3 hv1 heq
    have hfail :=
      not_alaogluErdosConjecture_iff_exists_threeFree_localized_radical.mpr
        ⟨v, b, A, hv3, hv1, heq⟩
    exact hfail hconj
  · intro hexcl
    by_contra hfail
    obtain ⟨v, b, A, hv3, hv1, heq⟩ :=
      not_alaogluErdosConjecture_iff_exists_threeFree_localized_radical.mp hfail
    exact hexcl v b A hv3 hv1 heq

end

end LeanProofs.TwoBaseIntegerExponent
