import ExponentialIdentities.IntegerExponent
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Partial results on integral powers at two and three

The conjecture that integrality of `2 ^ x` and `3 ^ x` forces a real exponent `x` to be an
integer is the classical Alaoglu--Erdős conjecture.  It is a special case of the four
exponentials conjecture and is not presently known in full.

This file establishes unconditional, quantitative partial results.  In particular, an integral
power strictly between two consecutive integral powers of a natural base must be at least one
unit from either endpoint.  Dividing by the lower endpoint gives explicit constraints on the
fractional part of any hypothetical counterexample.  Two further results approach the conjecture
from complementary directions:

* exact natural-power certificates rule out every counterexample with `2 ^ x < 10`, and
* the second finite difference of `m ↦ m ^ (log 3 / log 2)` lies strictly between zero and one,
  so at most two of every three consecutive natural candidates can satisfy the second integrality
  condition.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The full Alaoglu--Erdős conjecture, recorded as a proposition without asserting it as an
axiom.  The results below prove unconditional restrictions on any counterexample. -/
def AlaogluErdosConjecture : Prop :=
  ∀ {x : ℝ},
    (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
    (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
    x ∈ Set.range ((↑) : ℤ → ℝ)

/-- Integrality of a real power is preserved when its exponent is multiplied by a natural
number.  In particular, every hypothetical two-base counterexample produces all of its natural
multiples as further solutions. -/
theorem rpow_integer_nat_mul {b : ℕ} {x : ℝ}
    (h : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ x) (k : ℕ) :
    ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ ((k : ℝ) * x) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z ^ k, ?_⟩
  rw [Int.cast_pow, hz, mul_comm]
  exact (Real.rpow_mul_natCast (Nat.cast_nonneg b) x k).symm

/-- Any nonintegral exponent having an integral power of two must be irrational.  Thus a
counterexample to the two-base conjecture cannot be rational. -/
theorem irrational_of_not_integer_of_two_rpow_integer {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x) :
    Irrational x := by
  intro hxrat
  exact hx (IntegerExponent.integer_of_rational_of_two_rpow_integer hxrat h₂)

private lemma two_rpow_three_halves_lt_three :
    (2 : ℝ) ^ (3 / 2 : ℝ) < 3 := by
  apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_natCast]

private lemma three_lt_two_rpow_eight_fifths :
    (3 : ℝ) < (2 : ℝ) ^ (8 / 5 : ℝ) := by
  apply (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 3)
    (Real.rpow_nonneg (by norm_num) _) (by norm_num : (5 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_natCast]

private lemma five_lt_three_rpow_three_halves :
    (5 : ℝ) < (3 : ℝ) ^ (3 / 2 : ℝ) := by
  apply (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 5)
    (Real.rpow_nonneg (by norm_num) _) (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num [Real.rpow_natCast]

private lemma three_rpow_eight_fifths_lt_six :
    (3 : ℝ) ^ (8 / 5 : ℝ) < 6 := by
  apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (5 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num [Real.rpow_natCast]

/-- If `n < n + t < n + 1` and `b ^ (n + t)` is an integer, that integer stays one
full unit away from both neighboring integral powers. -/
theorem rpow_integer_gap_between_consecutive_powers
    {b n : ℕ} (hb : 1 < b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hint : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ ((n : ℝ) + t)) :
    (b : ℝ) ^ n + 1 ≤ (b : ℝ) ^ ((n : ℝ) + t) ∧
      (b : ℝ) ^ ((n : ℝ) + t) + 1 ≤ (b : ℝ) ^ (n + 1) := by
  obtain ⟨z, hz⟩ := hint
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hlo : (b : ℝ) ^ n < (b : ℝ) ^ ((n : ℝ) + t) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt hbR (by linarith)
  have hhi : (b : ℝ) ^ ((n : ℝ) + t) < (b : ℝ) ^ (n + 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt hbR
    push_cast
    linarith
  have hzlo : ((b ^ n : ℕ) : ℤ) < z := by
    exact_mod_cast hlo.trans_eq hz.symm
  have hzhi : z < ((b ^ (n + 1) : ℕ) : ℤ) := by
    exact_mod_cast hz.trans_lt hhi
  constructor
  · rw [← hz]
    exact_mod_cast (show ((b ^ n : ℕ) : ℤ) + 1 ≤ z by omega)
  · rw [← hz]
    exact_mod_cast (show z + 1 ≤ ((b ^ (n + 1) : ℕ) : ℤ) by omega)

/-- Normalized version of `rpow_integer_gap_between_consecutive_powers`: the fractional
part `t` is bounded away from both `0` and `1` by explicit inverse-power gaps. -/
theorem rpow_fractional_part_gap
    {b n : ℕ} (hb : 1 < b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hint : ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ ((n : ℝ) + t)) :
    1 + 1 / (b : ℝ) ^ n ≤ (b : ℝ) ^ t ∧
      (b : ℝ) ^ t ≤ (b : ℝ) - 1 / (b : ℝ) ^ n := by
  have hgap := rpow_integer_gap_between_consecutive_powers hb ht0 ht1 hint
  have hb0 : (0 : ℝ) < b := by positivity
  have hp : 0 < (b : ℝ) ^ n := pow_pos hb0 _
  have hfactor : (b : ℝ) ^ ((n : ℝ) + t) =
      (b : ℝ) ^ n * (b : ℝ) ^ t := by
    rw [Real.rpow_add hb0, Real.rpow_natCast]
  rw [hfactor] at hgap
  constructor
  · calc
      1 + 1 / (b : ℝ) ^ n = ((b : ℝ) ^ n + 1) / (b : ℝ) ^ n := by
        field_simp
      _ ≤ ((b : ℝ) ^ n * (b : ℝ) ^ t) / (b : ℝ) ^ n :=
        div_le_div_of_nonneg_right hgap.1 hp.le
      _ = (b : ℝ) ^ t := by field_simp
  · have hproduct :
        (b : ℝ) ^ n * (b : ℝ) ^ t ≤
          (b : ℝ) ^ n * (b : ℝ) - 1 := by
        rw [pow_succ] at hgap
        linarith [hgap.2]
    calc
      (b : ℝ) ^ t =
          ((b : ℝ) ^ n * (b : ℝ) ^ t) / (b : ℝ) ^ n := by
        field_simp
      _ ≤ (((b : ℝ) ^ n * (b : ℝ)) - 1) / (b : ℝ) ^ n :=
        div_le_div_of_nonneg_right hproduct hp.le
      _ = (b : ℝ) - 1 / (b : ℝ) ^ n := by field_simp

/-- Simultaneous explicit gaps supplied by integral powers at bases two and three. -/
theorem two_three_fractional_part_gaps
    {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ ((n : ℝ) + t))
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ ((n : ℝ) + t)) :
    (1 + 1 / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ t ∧
      (2 : ℝ) ^ t ≤ 2 - 1 / (2 : ℝ) ^ n) ∧
    (1 + 1 / (3 : ℝ) ^ n ≤ (3 : ℝ) ^ t ∧
      (3 : ℝ) ^ t ≤ 3 - 1 / (3 : ℝ) ^ n) := by
  exact ⟨rpow_fractional_part_gap (by norm_num) ht0 ht1 h₂,
    rpow_fractional_part_gap (by norm_num) ht0 ht1 h₃⟩

/-- The same bounds stated directly for an exponent strictly between `n` and `n + 1`. -/
theorem two_three_rpow_gaps_near_nat
    {x : ℝ} (n : ℕ) (hnx : (n : ℝ) < x) (hxn : x < (n : ℝ) + 1)
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    (1 + 1 / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (x - n) ∧
      (2 : ℝ) ^ (x - n) ≤ 2 - 1 / (2 : ℝ) ^ n) ∧
    (1 + 1 / (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (x - n) ∧
      (3 : ℝ) ^ (x - n) ≤ 3 - 1 / (3 : ℝ) ^ n) := by
  have ht0 : 0 < x - (n : ℝ) := sub_pos.mpr hnx
  have ht1 : x - (n : ℝ) < 1 := by linarith
  have h₂' : ∃ z : ℤ, (z : ℝ) =
      (2 : ℝ) ^ ((n : ℝ) + (x - (n : ℝ))) := by
    obtain ⟨z, hz⟩ := h₂
    refine ⟨z, ?_⟩
    rw [show (n : ℝ) + (x - (n : ℝ)) = x by ring]
    exact hz
  have h₃' : ∃ z : ℤ, (z : ℝ) =
      (3 : ℝ) ^ ((n : ℝ) + (x - (n : ℝ))) := by
    obtain ⟨z, hz⟩ := h₃
    refine ⟨z, ?_⟩
    rw [show (n : ℝ) + (x - (n : ℝ)) = x by ring]
    exact hz
  exact two_three_fractional_part_gaps ht0 ht1 h₂' h₃'

/-- The exponent which turns powers of two into the corresponding powers of three. -/
noncomputable def logThreeDivLogTwo : ℝ := Real.log 3 / Real.log 2

theorem one_lt_logThreeDivLogTwo : 1 < logThreeDivLogTwo := by
  rw [logThreeDivLogTwo]
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  simpa using Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)

theorem logThreeDivLogTwo_lt_eight_fifths :
    logThreeDivLogTwo < (8 / 5 : ℝ) := by
  rw [logThreeDivLogTwo]
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 3)
    three_lt_two_rpow_eight_fifths
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  exact hlog

private theorem alpha_mul_sub_one_lt_one :
    logThreeDivLogTwo * (logThreeDivLogTwo - 1) < 1 := by
  have hprod : 0 < ((8 / 5 : ℝ) - logThreeDivLogTwo) *
      (logThreeDivLogTwo + 3 / 5) :=
    mul_pos (sub_pos.mpr logThreeDivLogTwo_lt_eight_fifths)
      (by linarith [one_lt_logThreeDivLogTwo])
  nlinarith

private theorem exists_second_difference_point (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℝ, 1 < d ∧
      ((n + 2 : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + 1 : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo =
        logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          d ^ (logThreeDivLogTwo - 2) := by
  let α : ℝ := logThreeDivLogTwo
  let f : ℝ → ℝ := fun y ↦ y ^ α
  let g : ℝ → ℝ := fun y ↦ f (y + 1) - f y
  let g' : ℝ → ℝ := fun y ↦ α * ((y + 1) ^ (α - 1) - y ^ (α - 1))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt g (g' y) y := by
    have houter := Real.hasDerivAt_rpow_const (x := y + 1) (p := α)
      (Or.inl (by linarith : y + 1 ≠ 0))
    have hshift : HasDerivAt (fun z : ℝ ↦ (z + 1) ^ α)
        (α * (y + 1) ^ (α - 1)) y := by
      exact houter.comp_add_const y 1
    have hbase := Real.hasDerivAt_rpow_const (x := y) (p := α) (Or.inl hy.ne')
    convert hshift.sub hbase using 1 <;>
      first
      | rfl
      | exact Subsingleton.elim _ _
      | ring
  have hg_cont : ContinuousOn g (Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro y hy
    exact (hg_deriv y (hnpos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope g g'
    (by linarith : (n : ℝ) < (n : ℝ) + 1) hg_cont (by
      intro y hy
      exact hg_deriv y (hnpos.trans hy.1))
  have hcpos : 0 < c := hnpos.trans hc.1
  let h : ℝ → ℝ := fun y ↦ y ^ (α - 1)
  let h' : ℝ → ℝ := fun y ↦ (α - 1) * y ^ (α - 2)
  have hh_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt h (h' y) y := by
    have hp := Real.hasDerivAt_rpow_const (x := y) (p := α - 1) (Or.inl hy.ne')
    change HasDerivAt (fun y : ℝ ↦ y ^ (α - 1)) ((α - 1) * y ^ (α - 2)) y
    rw [show α - 1 - 1 = α - 2 by ring] at hp
    exact hp
  have hh_cont : ContinuousOn h (Icc c (c + 1)) := by
    intro y hy
    exact (hh_deriv y (hcpos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hdEq⟩ := exists_hasDerivAt_eq_slope h h'
    (by linarith : c < c + 1) hh_cont (by
      intro y hy
      exact hh_deriv y (hcpos.trans hy.1))
  refine ⟨d, hnR.trans_lt (hc.1.trans hd.1), ?_⟩
  have hcEq' : g ((n : ℝ) + 1) - g n = g' c := by
    simpa using hcEq.symm
  have hdEq' : h (c + 1) - h c = h' d := by
    simpa using hdEq.symm
  dsimp only [g', h'] at hcEq' hdEq'
  dsimp only [g, f, h, α] at hcEq' hdEq' ⊢
  rw [hdEq'] at hcEq'
  push_cast at hcEq' ⊢
  ring_nf at hcEq' ⊢
  exact hcEq'

/-- The second finite difference of `n ↦ n ^ (log 3 / log 2)` lies strictly between
zero and one at every positive integer. -/
theorem second_difference_logThreeDivLogTwo (n : ℕ) (hn : 1 ≤ n) :
    0 < ((n + 2 : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + 1 : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo ∧
      ((n + 2 : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + 1 : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo < 1 := by
  obtain ⟨d, hd1, hdEq⟩ := exists_second_difference_point n hn
  have hα0 : 0 < logThreeDivLogTwo := lt_trans zero_lt_one one_lt_logThreeDivLogTwo
  have hα1 : 0 < logThreeDivLogTwo - 1 := sub_pos.mpr one_lt_logThreeDivLogTwo
  have hαtwo : logThreeDivLogTwo - 2 < 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hdpow0 : 0 < d ^ (logThreeDivLogTwo - 2) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hd1) _
  have hdpow1 : d ^ (logThreeDivLogTwo - 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hd1 hαtwo
  constructor
  · rw [hdEq]
    positivity
  · rw [hdEq]
    calc
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          d ^ (logThreeDivLogTwo - 2) ≤
          logThreeDivLogTwo * (logThreeDivLogTwo - 1) * 1 := by
        gcongr
      _ < 1 := by simpa using alpha_mul_sub_one_lt_one

/-- Three consecutive values of `m ^ (log 3 / log 2)` cannot all be integers. -/
theorem not_three_consecutive_logThreeDivLogTwo_rpow_integers
    (n : ℕ) (hn : 1 ≤ n)
    (h₀ : ∃ z : ℤ, (z : ℝ) = (n : ℝ) ^ logThreeDivLogTwo)
    (h₁ : ∃ z : ℤ, (z : ℝ) = ((n + 1 : ℕ) : ℝ) ^ logThreeDivLogTwo)
    (h₂ : ∃ z : ℤ, (z : ℝ) = ((n + 2 : ℕ) : ℝ) ^ logThreeDivLogTwo) :
    False := by
  obtain ⟨z₀, hz₀⟩ := h₀
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨hpos, hlt⟩ := second_difference_logThreeDivLogTwo n hn
  have hzpos : (0 : ℤ) < z₂ - 2 * z₁ + z₀ := by
    exact_mod_cast (show (0 : ℝ) <
      (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) by
        rw [hz₂, hz₁, hz₀]
        exact hpos)
  have hzlt : z₂ - 2 * z₁ + z₀ < (1 : ℤ) := by
    exact_mod_cast (show
      (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) < 1 by
        rw [hz₂, hz₁, hz₀]
        exact hlt)
  omega

/-- The unique exponent for which the power of two has the prescribed positive natural value. -/
noncomputable def twoBaseCandidateExponent (m : ℕ) : ℝ := Real.logb 2 m

/-- A natural value `m` is a one-base candidate when the corresponding power of three is also an
integer.  Thus this predicate parametrizes the original problem by the integral value `m = 2 ^ x`.
-/
def TwoBaseNaturalCandidate (m : ℕ) : Prop :=
  0 < m ∧ (m : ℝ) ^ logThreeDivLogTwo ∈ Set.range ((↑) : ℤ → ℝ)

theorem two_rpow_twoBaseCandidateExponent {m : ℕ} (hm : 0 < m) :
    (2 : ℝ) ^ twoBaseCandidateExponent m = m := by
  rw [twoBaseCandidateExponent]
  exact Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hm)

theorem three_rpow_twoBaseCandidateExponent {m : ℕ} (hm : 0 < m) :
    (3 : ℝ) ^ twoBaseCandidateExponent m = (m : ℝ) ^ logThreeDivLogTwo := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [twoBaseCandidateExponent, Real.logb, logThreeDivLogTwo,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_def_of_pos hmR]
  congr 1
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- Every natural candidate produces an exponent satisfying both original integrality
hypotheses. -/
theorem TwoBaseNaturalCandidate.integer_powers {m : ℕ} (hm : TwoBaseNaturalCandidate m) :
    (2 : ℝ) ^ twoBaseCandidateExponent m ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ twoBaseCandidateExponent m ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · refine ⟨m, ?_⟩
    exact (two_rpow_twoBaseCandidateExponent hm.1).symm
  · rw [three_rpow_twoBaseCandidateExponent hm.1]
    exact hm.2

/-- Every exponent satisfying the two integrality hypotheses is represented by a positive
natural candidate `m = 2 ^ x`. -/
theorem exists_twoBaseNaturalCandidate_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∃ m : ℕ, 0 < m ∧ TwoBaseNaturalCandidate m ∧ x = twoBaseCandidateExponent m := by
  obtain ⟨z, hz⟩ := h₂
  have hzpos : 0 < z := by
    exact_mod_cast (hz.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
  have hm : 0 < m := by exact_mod_cast hzpos
  have hx : x = twoBaseCandidateExponent m :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      (hz.symm.trans (two_rpow_twoBaseCandidateExponent hm).symm)
  refine ⟨m, hm, ⟨hm, ?_⟩, hx⟩
  rw [← three_rpow_twoBaseCandidateExponent hm, ← hx]
  exact h₃

/-- Candidate-sequence reformulation of the full conjecture: it is equivalent to saying that
every positive natural `m` for which `m ^ (log 3 / log 2)` is integral is a power of two. -/
theorem alaogluErdosConjecture_iff_candidates_are_powers_of_two :
    AlaogluErdosConjecture ↔
      ∀ m : ℕ, TwoBaseNaturalCandidate m → ∃ n : ℕ, m = 2 ^ n := by
  constructor
  · intro h m hm
    obtain ⟨hx₂, hx₃⟩ := hm.integer_powers
    obtain ⟨z, hz⟩ := h hx₂ hx₃
    have hxnonneg : 0 ≤ twoBaseCandidateExponent m :=
      IntegerExponent.nonneg_of_two_rpow_integer hx₂
    have hznonnegR : (0 : ℝ) ≤ z := by rw [hz]; exact hxnonneg
    have hznonneg : 0 ≤ z := by exact_mod_cast hznonnegR
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg
    have hz' : (n : ℝ) = twoBaseCandidateExponent m := by
      calc
        (n : ℝ) = (((n : ℕ) : ℤ) : ℝ) := by norm_num
        _ = twoBaseCandidateExponent m := hz
    refine ⟨n, ?_⟩
    have hpow : (m : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
      calc
        (m : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m :=
          (two_rpow_twoBaseCandidateExponent hm.1).symm
        _ = (2 : ℝ) ^ (n : ℝ) := by rw [← hz']
        _ = ((2 ^ n : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    exact_mod_cast hpow
  · intro h x h₂ h₃
    obtain ⟨m, hmpos, hm, hx⟩ :=
      exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
    obtain ⟨n, hmn⟩ := h m hm
    have hexp : twoBaseCandidateExponent m = (n : ℝ) :=
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective (by
        calc
          (2 : ℝ) ^ twoBaseCandidateExponent m = (m : ℝ) :=
            two_rpow_twoBaseCandidateExponent hmpos
          _ = ((2 ^ n : ℕ) : ℝ) := by rw [hmn]
          _ = (2 : ℝ) ^ (n : ℝ) := by rw [Real.rpow_natCast]; norm_cast)
    refine ⟨n, ?_⟩
    rw [hx, hexp]
    norm_cast

/-- The offsets `0`, `1`, or `2` which yield candidates in the `k`-th aligned block of three
positive natural values. -/
noncomputable def twoBaseNaturalCandidateOffsetsInBlock (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range 3).filter fun j ↦ TwoBaseNaturalCandidate (3 * k + j + 1)

/-- In every aligned block of three positive natural candidates, at most two can give an integral
power of three. -/
theorem twoBaseNaturalCandidate_block_card_le_two (k : ℕ) :
    (twoBaseNaturalCandidateOffsetsInBlock k).card ≤ 2 := by
  classical
  let s := (Finset.range 3).filter fun j ↦ TwoBaseNaturalCandidate (3 * k + j + 1)
  change s.card ≤ 2
  have hsub : s ⊆ Finset.range 3 := Finset.filter_subset _ _
  by_contra hle
  have hcard : s.card = 3 := by
    have hlow : 3 ≤ s.card := by omega
    have hupp : s.card ≤ 3 := by
      simpa [s] using Finset.card_le_card hsub
    omega
  have hs : s = Finset.range 3 :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have hmem (j : ℕ) (hj : j < 3) : TwoBaseNaturalCandidate (3 * k + j + 1) := by
    have : j ∈ s := by rw [hs]; simpa using hj
    exact (Finset.mem_filter.mp this).2
  apply not_three_consecutive_logThreeDivLogTwo_rpow_integers (3 * k + 1) (by omega)
  · simpa [TwoBaseNaturalCandidate] using (hmem 0 (by omega)).2
  · simpa [TwoBaseNaturalCandidate] using (hmem 1 (by omega)).2
  · have h := hmem 2 (by omega)
    have heq : 3 * k + 2 + 1 = 3 * k + 1 + 2 := by omega
    rw [heq] at h
    simpa [TwoBaseNaturalCandidate] using h.2

/-- Blockwise counting form of the `2/3` upper-density result: among the first `N` disjoint
blocks of three positive candidates, at most `2 * N` have an integral corresponding power of
three. -/
theorem twoBaseNaturalCandidate_block_count_le (N : ℕ) :
    ∑ k ∈ Finset.range N, (twoBaseNaturalCandidateOffsetsInBlock k).card ≤
      2 * N := by
  calc
    ∑ k ∈ Finset.range N, (twoBaseNaturalCandidateOffsetsInBlock k).card ≤
        ∑ _k ∈ Finset.range N, 2 := by
      exact Finset.sum_le_sum fun k _ ↦ twoBaseNaturalCandidate_block_card_le_two k
    _ = 2 * N := by simp [mul_comm]

/-- The positive natural candidates not exceeding `3 * N`. -/
noncomputable def twoBaseNaturalCandidatesIcc (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (3 * N)).filter TwoBaseNaturalCandidate

/-- Concrete `2/3` counting bound: among the positive integers at most `3 * N`, at most
`2 * N` are two-base natural candidates. -/
theorem twoBaseNaturalCandidate_Icc_card_le (N : ℕ) :
    (twoBaseNaturalCandidatesIcc N).card ≤ 2 * N := by
  classical
  let block : ℕ → Finset ℕ := fun k ↦
    (twoBaseNaturalCandidateOffsetsInBlock k).image (fun j ↦ 3 * k + j + 1)
  let blocks : Finset ℕ := (Finset.range N).biUnion block
  have hsub : twoBaseNaturalCandidatesIcc N ⊆ blocks := by
    intro m hm
    have hm' : m ∈ (Finset.Icc 1 (3 * N)).filter TwoBaseNaturalCandidate := by
      simpa only [twoBaseNaturalCandidatesIcc] using hm
    obtain ⟨hmIcc, hmCand⟩ := Finset.mem_filter.mp hm'
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
    have hmN : m ≤ 3 * N := (Finset.mem_Icc.mp hmIcc).2
    let k : ℕ := (m - 1) / 3
    let j : ℕ := (m - 1) % 3
    have hk : k < N := by
      dsimp only [k]
      omega
    have hj : j < 3 := by
      dsimp only [j]
      omega
    have heq : 3 * k + j + 1 = m := by
      dsimp only [k, j]
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, heq⟩
    simp only [twoBaseNaturalCandidateOffsetsInBlock, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, heq ▸ hmCand⟩
  calc
    (twoBaseNaturalCandidatesIcc N).card ≤ blocks.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range N, (block k).card := Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range N, (twoBaseNaturalCandidateOffsetsInBlock k).card := by
      apply Finset.sum_congr rfl
      intro k _hk
      dsimp only [block]
      exact Finset.card_image_of_injective _ (by
        intro i j hij
        change 3 * k + i + 1 = 3 * k + j + 1 at hij
        omega)
    _ ≤ 2 * N := twoBaseNaturalCandidate_block_count_le N

/-- Below exponent two, integral powers at two and three force exponent zero or one. -/
theorem eq_zero_or_one_of_lt_two_of_two_three_rpow_integer {x : ℝ}
    (hxlt : x < 2)
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    x = 0 ∨ x = 1 := by
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  obtain ⟨z₂, hz₂⟩ := h₂
  have hpow_low : (1 : ℝ) ≤ (2 : ℝ) ^ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hx0
  have hpow_high : (2 : ℝ) ^ x < 4 := by
    calc
      (2 : ℝ) ^ x < (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxlt
      _ = 4 := by norm_num [Real.rpow_natCast]
  have hz₂low : (1 : ℤ) ≤ z₂ := by
    exact_mod_cast (hz₂.symm ▸ hpow_low)
  have hz₂high : z₂ < (4 : ℤ) := by
    exact_mod_cast (hz₂.symm ▸ hpow_high)
  rcases (show z₂ = 1 ∨ z₂ = 2 ∨ z₂ = 3 by omega) with h1 | h2 | h3
  · subst z₂
    left
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    simpa using hz₂.symm
  · subst z₂
    right
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    simpa using hz₂.symm
  · subst z₂
    have hxlow : (3 / 2 : ℝ) < x := by
      apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
      exact two_rpow_three_halves_lt_three.trans_eq hz₂
    have hxhigh : x < (8 / 5 : ℝ) := by
      apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
      exact hz₂.symm.trans_lt three_lt_two_rpow_eight_fifths
    obtain ⟨z₃, hz₃⟩ := h₃
    have hz₃lowR : (5 : ℝ) < (3 : ℝ) ^ x :=
      five_lt_three_rpow_three_halves.trans
        (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) hxlow)
    have hz₃highR : (3 : ℝ) ^ x < 6 :=
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) hxhigh).trans
        three_rpow_eight_fifths_lt_six
    have hz₃low : (5 : ℤ) < z₃ := by
      exact_mod_cast (hz₃.symm ▸ hz₃lowR)
    have hz₃high : z₃ < (6 : ℤ) := by
      exact_mod_cast (hz₃.symm ▸ hz₃highR)
    omega

private theorem no_integer_strictly_between_consecutive_naturals
    {y : ℝ} {a : ℕ}
    (hy : y ∈ Set.range ((↑) : ℤ → ℝ))
    (hlow : (a : ℝ) < y) (hupp : y < (a + 1 : ℕ)) : False := by
  obtain ⟨z, rfl⟩ := hy
  have hzlow : (a : ℤ) < z := by exact_mod_cast hlow
  have hzupp : z < (a : ℤ) + 1 := by exact_mod_cast hupp
  omega

private theorem mul_log_lt_mul_log_of_pow_lt
    {a b p q : ℕ} (ha : 0 < a) (hb : 0 < b) (hpow : a ^ p < b ^ q) :
    (p : ℝ) * Real.log (a : ℝ) < (q : ℝ) * Real.log (b : ℝ) := by
  have hpowR : (a : ℝ) ^ p < (b : ℝ) ^ q := by exact_mod_cast hpow
  have hlog := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using (show 0 < (a : ℝ) ^ p by positivity))
    (by simpa only [Set.mem_Ioi] using (show 0 < (b : ℝ) ^ q by positivity)) hpowR
  simpa only [Real.log_pow] using hlog

/-- The exact power inequalities supplied to this lemma trap `3 ^ x` strictly between `a` and
`a + 1`, contradicting its integrality.  The shared exponents 19/12 and 27/17 bracket
`log 3 / log 2`. -/
private theorem not_three_rpow_integer_of_two_rpow_eq
    {x : ℝ} {m a : ℕ}
    (h₂ : (2 : ℝ) ^ x = (m : ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (ha : 0 < a) (hxnonneg : 0 ≤ x)
    (hmLower : a ^ 12 < m ^ 19)
    (hmUpper : m ^ 27 < (a + 1) ^ 17) : False := by
  have hlogm := congrArg Real.log h₂
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlogm
  have hcommonLower :
      (19 : ℝ) * Real.log 2 < 12 * Real.log 3 :=
    mul_log_lt_mul_log_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  have hcommonUpper :
      (17 : ℝ) * Real.log 3 < 27 * Real.log 2 :=
    mul_log_lt_mul_log_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  have hmLowerLog :
      (12 : ℝ) * Real.log a < 19 * Real.log m :=
    mul_log_lt_mul_log_of_pow_lt (by omega) (by
      by_contra hm
      simp_all) hmLower
  have hmUpperLog :
      (27 : ℝ) * Real.log m < 17 * Real.log ((a + 1 : ℕ) : ℝ) :=
    mul_log_lt_mul_log_of_pow_lt (by
      by_contra hm
      simp_all) (by omega) hmUpper
  have hLowerLog : Real.log a < x * Real.log 3 := by
    apply lt_of_mul_lt_mul_left _ (by norm_num : (0 : ℝ) ≤ 12)
    calc
      (12 : ℝ) * Real.log a < 19 * Real.log m := hmLowerLog
      _ = x * (19 * Real.log 2) := by rw [← hlogm]; ring
      _ ≤ x * (12 * Real.log 3) := mul_le_mul_of_nonneg_left hcommonLower.le hxnonneg
      _ = 12 * (x * Real.log 3) := by ring
  have hUpperLog : x * Real.log 3 < Real.log ((a + 1 : ℕ) : ℝ) := by
    apply lt_of_mul_lt_mul_left _ (by norm_num : (0 : ℝ) ≤ 17)
    calc
      (17 : ℝ) * (x * Real.log 3) = x * (17 * Real.log 3) := by ring
      _ ≤ x * (27 * Real.log 2) := mul_le_mul_of_nonneg_left hcommonUpper.le hxnonneg
      _ = 27 * Real.log m := by rw [← hlogm]; ring
      _ < 17 * Real.log ((a + 1 : ℕ) : ℝ) := hmUpperLog
  have hLower : (a : ℝ) < (3 : ℝ) ^ x := by
    rw [Real.lt_rpow_iff_log_lt (by positivity) (by norm_num : (0 : ℝ) < 3)]
    exact hLowerLog
  have hUpper : (3 : ℝ) ^ x < (a + 1 : ℕ) := by
    rw [Real.rpow_lt_iff_lt_log (by norm_num : (0 : ℝ) < 3) (by positivity)]
    exact hUpperLog
  exact no_integer_strictly_between_consecutive_naturals h₃ hLower hUpper

/-- **A finite zero-free region for the Alaoglu--Erdős conjecture.**  If `2 ^ x` and
`3 ^ x` are integers and `2 ^ x < 10`, then `x` is an integer.  The proof checks the nine
possible positive integral values of `2 ^ x`; the five non-powers of two are excluded using
exact natural-power certificates. -/
theorem integer_of_two_three_rpow_integer_of_two_rpow_lt_ten {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hlt : (2 : ℝ) ^ x < 10) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨z, hz⟩ := h₂
  have hp : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)
  have hzlt : z < 10 := by exact_mod_cast (hz.symm ▸ hlt)
  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨z, hz⟩
  interval_cases z
  · refine ⟨0, ?_⟩
    norm_num at hz ⊢
    exact (Real.strictMono_rpow_of_base_gt_one (by norm_num)).injective
      (hz.symm.trans (by norm_num)) |>.symm
  · refine ⟨1, ?_⟩
    norm_num at hz ⊢
    exact (Real.strictMono_rpow_of_base_gt_one (by norm_num)).injective
      (hz.symm.trans (by norm_num)) |>.symm
  · exfalso
    exact not_three_rpow_integer_of_two_rpow_eq (m := 3) (a := 5) hz.symm h₃
      (by norm_num) hxnonneg (by norm_num) (by norm_num)
  · refine ⟨2, ?_⟩
    norm_num at hz ⊢
    exact (Real.strictMono_rpow_of_base_gt_one (by norm_num)).injective
      (hz.symm.trans (by norm_num)) |>.symm
  · exfalso
    exact not_three_rpow_integer_of_two_rpow_eq (m := 5) (a := 12) hz.symm h₃
      (by norm_num) hxnonneg (by norm_num) (by norm_num)
  · exfalso
    exact not_three_rpow_integer_of_two_rpow_eq (m := 6) (a := 17) hz.symm h₃
      (by norm_num) hxnonneg (by norm_num) (by norm_num)
  · exfalso
    exact not_three_rpow_integer_of_two_rpow_eq (m := 7) (a := 21) hz.symm h₃
      (by norm_num) hxnonneg (by norm_num) (by norm_num)
  · refine ⟨3, ?_⟩
    norm_num at hz ⊢
    exact (Real.strictMono_rpow_of_base_gt_one (by norm_num)).injective
      (hz.symm.trans (by norm_num)) |>.symm
  · exfalso
    exact not_three_rpow_integer_of_two_rpow_eq (m := 9) (a := 32) hz.symm h₃
      (by norm_num) hxnonneg (by norm_num) (by norm_num)

/-- Equivalently, a nonintegral two-base solution would have to satisfy `10 ≤ 2 ^ x`. -/
theorem ten_le_two_rpow_of_not_integer_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    10 ≤ (2 : ℝ) ^ x := by
  exact not_lt.mp fun hlt ↦ hx
    (integer_of_two_three_rpow_integer_of_two_rpow_lt_ten h₂ h₃ hlt)

/-- The finite zero-free region in exponent coordinates: a nonintegral two-base solution must lie
at or above `log 10 / log 2`. -/
theorem log_ten_div_log_two_le_of_not_integer_of_two_three_rpow_integer {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Real.log 10 / Real.log 2 ≤ x := by
  have hten := ten_le_two_rpow_of_not_integer_of_two_three_rpow_integer h₂ h₃ hx
  have hlog : Real.log 10 ≤ x * Real.log 2 :=
    (Real.le_rpow_iff_log_le (by norm_num : (0 : ℝ) < 10)
      (by norm_num : (0 : ℝ) < 2)).mp hten
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog

end LeanProofs.TwoBaseIntegerExponent
