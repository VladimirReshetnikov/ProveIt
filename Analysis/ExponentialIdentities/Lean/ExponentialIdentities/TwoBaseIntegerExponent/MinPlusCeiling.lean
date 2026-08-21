import ExponentialIdentities.TwoBaseIntegerExponent.Localization

/-!
# The min-plus ceiling: term-wise valuation can never beat archimedean size

Interpolation-determinant arguments in this corpus reach a contradiction by squeezing a nonzero
integer determinant `D` between a lower bound and an upper bound.  A recurring proposal is to
manufacture the lower bound from *p-adic content*: choose the nodes and the column exponents so
that every monomial in the Leibniz expansion of `D` is divisible by a high power of `2` and of
`3`, and conclude `|D| ≥ 2 ^ V₂ · 3 ^ V₃` from the min-plus estimate
`v_p(D) ≥ min_σ ∑_i v_p(E_{i σ i})`.

This module records why that proposal cannot work, in the strongest and simplest form.  For a
nonzero integer `D` the `{2,3}`-part of `D` divides `D`, so

    v₂(D) + θ · v₃(D) ≤ log₂ |D|,     θ = log₂ 3.

Min-plus estimates are *lower* bounds for `v₂(D)` and `v₃(D)`, and any archimedean estimate is
an *upper* bound for `log₂ |D|`.  The two therefore can never be inconsistent, whatever the node
system, whatever the column set, and whatever primes are used: the p-adic content of an integer
is bounded by the integer.

The consequence for the program is sharper than a numerical shortfall.  Amplification can only
succeed when the archimedean bound used is genuinely *smaller* than the crude size of the
entries — that is, when real cancellation (divided differences, Schur factors) has been
exploited.  Term-wise divisibility alone contributes nothing beyond what `|D| ≥ 1` already gives.

`minPlusContent_le_of_abs_le` is the statement in the form a determinant argument consumes it;
`primeContent_le_log` is the same fact for an arbitrary finite set of primes.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The `{2,3}`-part of a natural number divides it. -/
theorem two_three_part_dvd (n : ℕ) :
    2 ^ n.factorization 2 * 3 ^ n.factorization 3 ∣ n :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.pow _ _ (by norm_num)) (Nat.ordProj_dvd n 2) (Nat.ordProj_dvd n 3)

/-- `logThreeDivLogTwo` is the base-two logarithm of three. -/
theorem logThreeDivLogTwo_eq_logb : logThreeDivLogTwo = Real.logb 2 3 := rfl

/-- **Content is bounded by size.**  The `{2,3}`-adic content of a positive natural number,
measured in base-two logarithms, is at most its base-two logarithm. -/
theorem two_three_content_le_logb {n : ℕ} (hn : n ≠ 0) :
    (n.factorization 2 : ℝ) + (n.factorization 3 : ℝ) * logThreeDivLogTwo
      ≤ Real.logb 2 n := by
  have hdvd := two_three_part_dvd n
  have hle : 2 ^ n.factorization 2 * 3 ^ n.factorization 3 ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hleR : ((2 : ℝ) ^ n.factorization 2) * ((3 : ℝ) ^ n.factorization 3) ≤ (n : ℝ) := by
    exact_mod_cast hle
  have hposL : (0 : ℝ) < ((2 : ℝ) ^ n.factorization 2) * ((3 : ℝ) ^ n.factorization 3) := by
    positivity
  have hmono := Real.logb_le_logb_right (b := 2) (by norm_num) hleR
  refine le_trans (le_of_eq ?_) hmono
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num) (by norm_num), logThreeDivLogTwo_eq_logb]
  ring

/-- **The min-plus ceiling.**  If a term-wise divisibility argument certifies that `2 ^ V₂` and
`3 ^ V₃` divide a nonzero integer `D`, and an archimedean argument certifies `|D| ≤ 2 ^ B`, then
necessarily `V₂ + V₃ · θ ≤ B`.

So no pair of such estimates is ever contradictory.  Term-wise p-adic amplification cannot, by
itself, close a determinant argument: whatever it certifies is already implied by the size of
`D`. -/
theorem minPlusContent_le_of_abs_le {D : ℤ} (hD : D ≠ 0) {V₂ V₃ : ℕ} {B : ℝ}
    (h₂ : (2 : ℤ) ^ V₂ ∣ D) (h₃ : (3 : ℤ) ^ V₃ ∣ D)
    (hB : |(D : ℝ)| ≤ (2 : ℝ) ^ B) :
    (V₂ : ℝ) + (V₃ : ℝ) * logThreeDivLogTwo ≤ B := by
  have hDn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have h₂n : 2 ^ V₂ ∣ D.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h₂
    simpa using this
  have h₃n : 3 ^ V₃ ∣ D.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h₃
    simpa using this
  have hV₂ : V₂ ≤ D.natAbs.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hDn).mp h₂n
  have hV₃ : V₃ ≤ D.natAbs.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hDn).mp h₃n
  have hcontent := two_three_content_le_logb hDn
  have hθpos : 0 < logThreeDivLogTwo := lt_trans zero_lt_one one_lt_logThreeDivLogTwo
  have hstep : (V₂ : ℝ) + (V₃ : ℝ) * logThreeDivLogTwo
      ≤ (D.natAbs.factorization 2 : ℝ)
        + (D.natAbs.factorization 3 : ℝ) * logThreeDivLogTwo := by
    have h2 : (V₂ : ℝ) ≤ (D.natAbs.factorization 2 : ℝ) := by exact_mod_cast hV₂
    have h3 : (V₃ : ℝ) ≤ (D.natAbs.factorization 3 : ℝ) := by exact_mod_cast hV₃
    have := mul_le_mul_of_nonneg_right h3 hθpos.le
    linarith
  have habs : ((D.natAbs : ℕ) : ℝ) = |(D : ℝ)| := by
    rw [Int.cast_natAbs]
    push_cast
    rfl
  have hbound : Real.logb 2 (D.natAbs : ℕ) ≤ B := by
    rw [habs]
    have hpos : (0 : ℝ) < |(D : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hD)
    have := Real.logb_le_logb_right (b := 2) (by norm_num) hB
    calc Real.logb 2 |(D : ℝ)| ≤ Real.logb 2 ((2 : ℝ) ^ B) := this
      _ = B := Real.logb_rpow (by norm_num)
  linarith [hstep, hcontent, hbound]

/-- The same ceiling for an arbitrary finite set of primes: no enlargement of the prime set
changes the conclusion, because the whole `S`-part of `n` still divides `n`. -/
theorem prod_primePow_dvd {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, p ^ n.factorization p ∣ n := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert p S hp ih =>
      have hSprime : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hpprime : p.Prime := hS p (Finset.mem_insert_self p S)
      have hcop : Nat.Coprime (p ^ n.factorization p) (∏ q ∈ S, q ^ n.factorization q) := by
        refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right ?_)
        intro q hq
        refine Nat.Coprime.pow_right _ ?_
        refine (Nat.coprime_primes hpprime (hSprime q hq)).mpr ?_
        rintro rfl
        exact hp hq
      rw [Finset.prod_insert hp]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Nat.ordProj_dvd n p) (ih hSprime)

/-- **All-primes form of the ceiling.**  The total logarithmic content of a positive natural
number over any finite set of primes is at most its logarithm. -/
theorem primeContent_le_log {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p ≤ Real.log n := by
  classical
  have hdvd := prod_primePow_dvd hn hS
  have hle : ∏ p ∈ S, p ^ n.factorization p ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hleR : ((∏ p ∈ S, p ^ n.factorization p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  have hpos : (0 : ℝ) < ((∏ p ∈ S, p ^ n.factorization p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ S, p ^ n.factorization p := by
      refine Finset.prod_pos ?_
      intro p hp
      exact pow_pos (hS p hp).pos _
    exact_mod_cast this
  have hlog := Real.log_le_log hpos hleR
  refine le_trans (le_of_eq ?_) hlog
  push_cast
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Real.log_pow]
  · intro p hp
    have : (0 : ℝ) < (p : ℝ) ^ n.factorization p := by
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hS p hp).pos
      positivity
    exact ne_of_gt this

end LeanProofs.TwoBaseIntegerExponent
