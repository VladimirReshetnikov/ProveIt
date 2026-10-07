import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRank_exceptional_numeric {s J : ℕ} {q c C m : ℝ}
    (hq : 2 ≤ q) (hc : 0 < c) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hthreshold : (s : ℝ) ^ (4 / c) ≤ q)
    (hJ : 2 * (C + m + 10) / c ≤ (J : ℝ)) :
    (s : ℝ) ^ (J + 1) * q ^ (C + m - c * J) ≤ q ^ (-(10 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hJc : 2 * (C + m + 10) ≤ c * J := by
    have := (div_le_iff₀ hc).mp hJ
    nlinarith only [this]
  have hJpos : 0 < J := by
    by_contra hz
    have hzero : J = 0 := by omega
    simp only [hzero, Nat.cast_zero, mul_zero] at hJc
    linarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
  have hs : (s : ℝ) ≤ q ^ (c / 4) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg s) _) hthreshold
      (show 0 ≤ c / 4 by positivity)
    rw [← Real.rpow_mul (Nat.cast_nonneg s)] at h
    have heq : 4 / c * (c / 4) = 1 := by field_simp
    simpa only [heq, Real.rpow_one] using h
  have hsJ : (s : ℝ) ^ (J + 1) ≤ q ^ (c / 4 * ((J + 1 : ℕ) : ℝ)) := by
    simpa only [Real.rpow_mul_natCast hq0.le] using
      pow_le_pow_left₀ (Nat.cast_nonneg s) hs (J + 1)
  have hexp : c / 4 * ((J + 1 : ℕ) : ℝ) + (C + m - c * J) ≤ -(10 : ℝ) := by
    push_cast
    have htwice : (J : ℝ) + 1 ≤ 2 * J := by linarith only [hJ1]
    have hmul := mul_le_mul_of_nonneg_left htwice (show 0 ≤ c / 4 by positivity)
    nlinarith only [hJc, hmul]
  calc
    _ ≤ q ^ (c / 4 * ((J + 1 : ℕ) : ℝ)) * q ^ (C + m - c * J) :=
      mul_le_mul_of_nonneg_right hsJ (Real.rpow_nonneg hq0.le _)
    _ = q ^ (c / 4 * ((J + 1 : ℕ) : ℝ) + (C + m - c * J)) := (Real.rpow_add hq0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 hexp

theorem finiteProbability_rank_markov {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (ρ : Ω → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    {q C : ℝ} (hq : 0 < q) :
    w.eventProbability (fun x => q ^ (-C) < ρ x) ≤ q ^ C * w.mean ρ := by
  change w.mean (fun x => if q ^ (-C) < ρ x then 1 else 0) ≤ _
  calc
    _ ≤ w.mean (fun x => q ^ C * ρ x) := by
      apply w.mean_mono
      intro x
      split_ifs with hx
      · have h := mul_le_mul_of_nonneg_left hx.le (Real.rpow_nonneg hq.le C)
        simpa only [← Real.rpow_add hq, add_neg_cancel, Real.rpow_zero] using h
      · exact mul_nonneg (Real.rpow_nonneg hq.le C) (hρ x)
    _ = _ := by
      simp only [FiniteProbabilityWeights.mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem modularRank_exceptional_probability {Ω Row : Type*} [Fintype Ω] [Fintype Row]
    (w : FiniteProbabilityWeights Ω) (ρ : Row → Ω → ℝ)
    (hρ : ∀ r x, 0 ≤ ρ r x) {s J : ℕ} {q c C m : ℝ}
    (hq : 2 ≤ q) (hc : 0 < c) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hthreshold : (s : ℝ) ^ (4 / c) ≤ q)
    (hJ : 2 * (C + m + 10) / c ≤ (J : ℝ))
    (hrows : (Fintype.card Row : ℝ) ≤ s * q ^ m)
    (hmean : ∀ r, w.mean (ρ r) ≤ ((s : ℝ) * q ^ (-c)) ^ J) :
    w.eventProbability (fun x => ∃ r, q ^ (-C) < ρ r x) ≤ q ^ (-(10 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hunion := w.eventProbability_union_bound
    (fun x => ∃ r, q ^ (-C) < ρ r x) (fun r x => q ^ (-C) < ρ r x)
    (fun _ h => h)
  have hrow (r) : w.eventProbability (fun x => q ^ (-C) < ρ r x) ≤
      q ^ C * ((s : ℝ) * q ^ (-c)) ^ J :=
    (finiteProbability_rank_markov w (ρ r) (hρ r) hq0).trans
      (mul_le_mul_of_nonneg_left (hmean r) (Real.rpow_nonneg hq0.le C))
  calc
    _ ≤ ∑ _r : Row, q ^ C * ((s : ℝ) * q ^ (-c)) ^ J :=
      hunion.trans (Finset.sum_le_sum (fun r _ => hrow r))
    _ = (Fintype.card Row : ℝ) * (q ^ C * ((s : ℝ) * q ^ (-c)) ^ J) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ ((s : ℝ) * q ^ m) * (q ^ C * ((s : ℝ) * q ^ (-c)) ^ J) :=
      mul_le_mul_of_nonneg_right hrows (by positivity)
    _ = (s : ℝ) ^ (J + 1) * q ^ (C + m - c * J) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hq0.le]
      rw [pow_succ]
      calc
        _ = (s : ℝ) ^ J * s * (q ^ m * q ^ C * q ^ (-c * J)) := by ring
        _ = _ := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 2; ring
    _ ≤ _ := modularRank_exceptional_numeric hq hc hC hm hthreshold hJ

noncomputable def modularRankSmallBallExponent (s : ℕ) : ℝ := (2 : ℝ) ^ (1 - (s : ℝ))

theorem modularRankSmallBallExponent_pos (s : ℕ) : 0 < modularRankSmallBallExponent s :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem modularRankSmallBallExponent_eq {s : ℕ} (hs : 0 < s) :
    modularRankSmallBallExponent s = 1 / (2 : ℝ) ^ (s - 1) := by
  have hexp : 1 - (s : ℝ) = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [modularRankSmallBallExponent, hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    one_div]

theorem modularRank_exceptional_probability_of_parameters
    {Ω Row : Type*} [Fintype Ω] [Fintype Row]
    (w : FiniteProbabilityWeights Ω) (ρ : Row → Ω → ℝ)
    (hρ : ∀ r x, 0 ≤ ρ r x) {s J : ℕ} {q C m : ℝ}
    (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hq : max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ q)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ J)
    (hrows : (Fintype.card Row : ℝ) ≤ s * q ^ m)
    (hmean : ∀ r, w.mean (ρ r) ≤ ((s : ℝ) * q ^ (-modularRankSmallBallExponent s)) ^ J) :
    w.eventProbability (fun x => ∃ r, q ^ (-C) < ρ r x) ≤ q ^ (-(10 : ℝ)) := by
  apply modularRank_exceptional_probability w ρ hρ
    ((le_max_left _ _).trans hq) (modularRankSmallBallExponent_pos s) hC hm
    ((le_max_right _ _).trans hq) _ hrows hmean
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hJ)

end Erdos3

end

section

namespace Erdos3

def modularInitialRankStrength (s d : ℕ) : ℕ :=
  2 ^ (2 * s) * s.factorial * (d + 2)

def modularInitialBlockCount (s d : ℕ) : ℕ :=
  2 ^ s * (modularInitialRankStrength s d + d + 10) + 1

theorem modularInitialRankStrength_exponent (s d : ℕ) :
    (modularInitialRankStrength s d : ℝ) /
      ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ) = d + 2 := by
  have hpow : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  simp only [modularInitialRankStrength, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add]
  rw [show 2 * s = s + s by omega, pow_add]
  field_simp

theorem modularInitialBlockCount_threshold {s : ℕ} (hs : 0 < s) (d : ℕ) :
    ⌈2 * ((modularInitialRankStrength s d : ℝ) + d + 10) /
      modularRankSmallBallExponent s⌉₊ ≤ modularInitialBlockCount s d := by
  apply Nat.ceil_le.mpr
  rw [modularRankSmallBallExponent_eq hs, div_div_eq_mul_div, div_one]
  have hpow : 2 * (2 : ℝ) ^ (s - 1) = (2 : ℝ) ^ s := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  calc
    _ = (2 : ℝ) ^ s * ((modularInitialRankStrength s d : ℝ) + d + 10) := by
      rw [← hpow]
      ring
    _ ≤ (modularInitialBlockCount s d : ℝ) := by
      simp only [modularInitialBlockCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one]
      linarith

theorem modularInitialBlockCount_linear_bound (s d : ℕ) :
    modularInitialBlockCount s d ≤
      (2 ^ s * (2 ^ (2 * s) * s.factorial + 1) + 1) * (d + 11) := by
  dsimp only [modularInitialBlockCount, modularInitialRankStrength]
  nlinarith [Nat.zero_le (2 ^ s), Nat.zero_le (2 ^ (2 * s) * s.factorial)]

end Erdos3

end

section

namespace Erdos3

theorem modularRank_tag_cost_le {s n a : ℕ} (hn : n + 1 ≤ s)
    {p : ℝ} (hp : 1 ≤ p) :
    ((n + 1 : ℕ) : ℝ) * p ^ (-(a : ℝ) / (2 : ℝ) ^ n) ≤
      (s : ℝ) * (p ^ a) ^ (-modularRankSmallBallExponent s) := by
  have hs : 0 < s := by omega
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (s - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : (a : ℝ) / (2 : ℝ) ^ (s - 1) ≤ (a : ℝ) / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg a) (by positivity) hpow
  have hphase : p ^ (-(a : ℝ) / (2 : ℝ) ^ n) ≤
      (p ^ a) ^ (-modularRankSmallBallExponent s) := by
    rw [modularRankSmallBallExponent_eq hs, ← Real.rpow_natCast_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp
    simpa only [neg_div, mul_neg, mul_one_div] using neg_le_neg hdiv
  exact mul_le_mul (by exact_mod_cast hn) hphase (Real.rpow_nonneg hp0.le _)
    (Nat.cast_nonneg s)

end Erdos3

end

section

namespace Erdos3

theorem modularInitialBlockCount_two_dimensions (m d : ℕ) :
    2 * d ≤ modularInitialBlockCount m d := by
  have ha : 1 ≤ 2 ^ (2 * m) * m.factorial := Nat.succ_le_of_lt (by positivity)
  have hb : 1 ≤ 2 ^ m := Nat.succ_le_of_lt (by positivity)
  have hr : d + 2 ≤ modularInitialRankStrength m d := by
    unfold modularInitialRankStrength
    nlinarith
  unfold modularInitialBlockCount
  nlinarith

namespace VectorPolynomial

def preparedSpatialKernelBlocks (m M nX : ℕ) :
    Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) where
  toFun z := ⟨(m + 1) * (m + 3) + (finProdFinEquiv z).val, by
    have hz := (finProdFinEquiv z).isLt
    have hdim := modularInitialBlockCount_two_dimensions m (nX + m * M)
    have hmul : modularInitialBlockCount m (nX + m * M) ≤
        (m + 1) * modularInitialBlockCount m (nX + m * M) := by
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)
    omega⟩
  inj' := by
    intro z w h
    apply finProdFinEquiv.injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega

theorem preparedSpatialKernelBlocks_outside_selection (m M nX s : ℕ) (hs : s ≤ m)
    (z : Fin 2 × Fin nX) :
    preparedSpatialKernelBlocks m M nX z ∉ Set.range
      (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) s hs) := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  change i.val = (m + 1) * (m + 3) + (finProdFinEquiv z).val at hv
  have hn : s + 1 ≤ (m + 1) * (m + 3) := by nlinarith
  have hi' := i.isLt
  omega

end VectorPolynomial
end Erdos3

end

end OAI
