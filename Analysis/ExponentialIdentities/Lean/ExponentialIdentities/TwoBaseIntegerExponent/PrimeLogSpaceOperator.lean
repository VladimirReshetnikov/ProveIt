import ExponentialIdentities.TwoBaseIntegerExponent.LogProductIndependence
import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.Real.Irrational

/-!
# An operator formulation on the prime-logarithm space

All the standard reformulations of the two-base conjecture are Diophantine.  This file records
a purely linear-algebraic one: the conjecture becomes a statement about multiplication by
`θ = log 3 / log 2` acting on a single `ℚ`-vector space.

Let `W = span_ℚ {log p : p prime} ⊆ ℝ`, which by unique factorization has the `log p` as a
basis.  Multiplication by `θ` does not preserve `W`, so consider the largest part of `W` that
it does return to `W`,
`U = {w ∈ W : θ * w ∈ W}`.
This is a `ℚ`-subspace, and it is never zero because `θ * log 2 = log 3 ∈ W`, so
`ℚ * log 2 ⊆ U`.  The rational-output form of the conjecture is exactly the assertion
`dim_ℚ U = 1`.

Rather than carrying `Submodule.rank` through the argument, the file states the two sides in
the elementary form the proof actually uses.  Membership in `W` is `InPrimeLogSpan`, and
`dim_ℚ U = 1` becomes `PrimeLogSpanThetaPullbackRankOne`: every `w` with `w ∈ W` and
`θ * w ∈ W` is a rational multiple of `log 2`.  Since `ℚ * log 2 ⊆ U` always holds
(`inPrimeLogSpan_theta_mul_rat_mul_logTwo`), this single inclusion is equivalent to
`U = ℚ * log 2`, hence to `dim_ℚ U = 1`.

The mechanism is denominator clearing, exactly as in the paper proof.  An element of `W` is
`w = ∑ p, c p * log p` with rational `c p`, almost all zero; clearing a common denominator `N`
gives `N * w = log v` for a positive rational `v`.  If also `θ * w ∈ W`, clearing a second
denominator `M` turns `θ * log (v ^ M) = log u` into `(v ^ M) ^ θ = u`, so `v ^ M` lies in the
multiplicative group `K = {v ∈ ℚ, 0 < v, v ^ θ ∈ ℚ}`.  Thus `U` is the `ℚ`-span of `log K`, and
`dim_ℚ U = 1` says `K` has rank one, which is the rational-output form of the conjecture.  That
transfer is `exists_nat_mul_eq_log_of_thetaPullback`, and the equivalence itself is
`primeLogSpanThetaPullbackRankOne_iff_rationalOutput`.

Nothing here asserts the conjecture: both sides are recorded as `Prop`s and only the
biconditional is proved.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- Membership in `W`, the `ℚ`-span of the prime logarithms inside `ℝ`. -/
def InPrimeLogSpan (w : ℝ) : Prop :=
  ∃ (S : Finset ℕ) (c : ℕ → ℚ), (∀ p ∈ S, Nat.Prime p) ∧
    w = ∑ p ∈ S, (c p : ℝ) * Real.log p

/-- **Operator form of the conjecture.**  Multiplication by `θ = log 3 / log 2` carries back
into `W` only the rational multiples of `log 2`.  Since the line `ℚ * log 2` always lies in the
pullback `U = {w ∈ W : θ * w ∈ W}` (see `inPrimeLogSpan_theta_mul_rat_mul_logTwo`), this is the
elementary form of `dim_ℚ U = 1`.  It is recorded as a `Prop`, never asserted. -/
def PrimeLogSpanThetaPullbackRankOne : Prop :=
  ∀ w : ℝ, InPrimeLogSpan w → InPrimeLogSpan (logThreeDivLogTwo * w) →
    ∃ q : ℚ, w = (q : ℝ) * Real.log 2

/-- **Rational-output form of the two-base conjecture.**  Rationality of both powers already
forces the exponent to be an integer.  This implies `AlaogluErdosConjecture` and is formally
stronger than it; it is recorded as a `Prop`, never asserted. -/
def RationalOutputTwoBaseConjecture : Prop :=
  ∀ x : ℝ, (∃ q : ℚ, ((q : ℚ) : ℝ) = (2 : ℝ) ^ x) →
    (∃ r : ℚ, ((r : ℚ) : ℝ) = (3 : ℝ) ^ x) → x ∈ Set.range ((↑) : ℤ → ℝ)

private theorem logTwo_ne_zero : Real.log 2 ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num))

/-- The defining property of `θ`: it sends `log 2` to `log 3`. -/
theorem theta_mul_logTwo : logThreeDivLogTwo * Real.log 2 = Real.log 3 := by
  rw [logThreeDivLogTwo]
  exact div_mul_cancel₀ _ logTwo_ne_zero

/-! ### The space `W` and the line `ℚ · log 2` -/

/-- Every rational multiple of `log 2` lies in `W`. -/
theorem inPrimeLogSpan_rat_mul_logTwo (q : ℚ) :
    InPrimeLogSpan ((q : ℝ) * Real.log 2) := by
  refine ⟨{2}, fun _ ↦ q, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact Nat.prime_two
  · simp

/-- Every rational multiple of `log 3` lies in `W`. -/
theorem inPrimeLogSpan_rat_mul_logThree (q : ℚ) :
    InPrimeLogSpan ((q : ℝ) * Real.log 3) := by
  refine ⟨{3}, fun _ ↦ q, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact Nat.prime_three
  · simp

/-- **The pullback is never zero.**  The line `ℚ * log 2` always lies in
`U = {w ∈ W : θ * w ∈ W}`, because `θ` carries it onto `ℚ * log 3 ⊆ W`. -/
theorem inPrimeLogSpan_theta_mul_rat_mul_logTwo (q : ℚ) :
    InPrimeLogSpan (logThreeDivLogTwo * ((q : ℝ) * Real.log 2)) := by
  have h : logThreeDivLogTwo * ((q : ℝ) * Real.log 2) = (q : ℝ) * Real.log 3 := by
    rw [← theta_mul_logTwo]
    ring
  rw [h]
  exact inPrimeLogSpan_rat_mul_logThree q

/-- The logarithm of a positive rational lies in `W`. -/
theorem inPrimeLogSpan_log_ratCast {v : ℚ} (hv : 0 < v) :
    InPrimeLogSpan (Real.log ((v : ℚ) : ℝ)) := by
  classical
  refine ⟨(v.num.toNat).primeFactors ∪ v.den.primeFactors,
    fun p ↦ ((v.num.toNat).factorization p : ℚ) - (v.den.factorization p : ℚ), ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact Nat.prime_of_mem_primeFactors h
  · rw [log_ratCast_eq_sum_of_subset hv Finset.subset_union_left Finset.subset_union_right]
    exact Finset.sum_congr rfl fun p _ ↦ by norm_cast

/-! ### Denominator clearing -/

/-- Multiplying a rational by any natural multiple of its denominator produces an integer. -/
private theorem exists_int_mul_of_den_dvd {c : ℚ} {N : ℕ} (h : c.den ∣ N) :
    ∃ e : ℤ, (N : ℚ) * c = (e : ℚ) := by
  obtain ⟨k, hk⟩ := h
  have hd : ((c.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
  have h1 : ((c.num : ℤ) : ℚ) = c * ((c.den : ℕ) : ℚ) := by
    rw [← div_eq_iff hd]
    exact Rat.num_div_den c
  refine ⟨(k : ℤ) * c.num, ?_⟩
  have hNq : ((N : ℕ) : ℚ) = ((c.den : ℕ) : ℚ) * ((k : ℕ) : ℚ) := by
    rw [hk]
    exact Nat.cast_mul c.den k
  rw [hNq]
  push_cast
  rw [h1]
  ring

/-- **Denominator clearing in `W`.**  Every member of `W` becomes the logarithm of a positive
rational after multiplication by a suitable positive integer. -/
theorem exists_nat_mul_eq_log_ratCast {w : ℝ} (hw : InPrimeLogSpan w) :
    ∃ N : ℕ, 0 < N ∧ ∃ v : ℚ, 0 < v ∧ (N : ℝ) * w = Real.log ((v : ℚ) : ℝ) := by
  classical
  obtain ⟨S, c, hSprime, hwsum⟩ := hw
  obtain ⟨N, hNpos, hNdvd⟩ : ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S, (c p).den ∣ N :=
    ⟨∏ p ∈ S, (c p).den, Finset.prod_pos fun p _ ↦ (c p).pos,
      fun p hp ↦ Finset.dvd_prod_of_mem (fun r ↦ (c r).den) hp⟩
  have hex : ∀ p ∈ S, ∃ e : ℤ, ((N : ℕ) : ℚ) * c p = (e : ℚ) :=
    fun p hp ↦ exists_int_mul_of_den_dvd (hNdvd p hp)
  choose! e he using hex
  have hposQ : ∀ p ∈ S, (0 : ℚ) < ((p : ℕ) : ℚ) := by
    intro p hp
    exact_mod_cast (hSprime p hp).pos
  have hposR : ∀ p ∈ S, (0 : ℝ) < ((p : ℕ) : ℝ) := by
    intro p hp
    exact_mod_cast (hSprime p hp).pos
  refine ⟨N, hNpos, ∏ p ∈ S, ((p : ℕ) : ℚ) ^ (e p), ?_, ?_⟩
  · exact Finset.prod_pos fun p hp ↦ zpow_pos (hposQ p hp) _
  · have hcast : ((∏ p ∈ S, ((p : ℕ) : ℚ) ^ (e p) : ℚ) : ℝ) =
        ∏ p ∈ S, (((p : ℕ) : ℝ) ^ (e p)) := by
      rw [Rat.cast_prod]
      exact Finset.prod_congr rfl fun p _ ↦ by rw [Rat.cast_zpow, Rat.cast_natCast]
    have hne : ∀ p ∈ S, (((p : ℕ) : ℝ) ^ (e p)) ≠ 0 :=
      fun p hp ↦ ne_of_gt (zpow_pos (hposR p hp) _)
    have hterm : ∀ p ∈ S, Real.log (((p : ℕ) : ℝ) ^ (e p)) = (e p : ℝ) * Real.log p :=
      fun p _ ↦ Real.log_zpow _ _
    rw [hcast, Real.log_prod hne, Finset.sum_congr rfl hterm, hwsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hR : ((N : ℕ) : ℝ) * (c p : ℝ) = (e p : ℝ) := by exact_mod_cast he p hp
    rw [← mul_assoc, hR]

/-! ### The pullback consists of logarithms of the group `K` -/

/-- **Transfer to the group `K`.**  If `w` lies in `W` and `θ * w` lies in `W`, then some
positive integer multiple of `w` is `log v` for a positive rational `v` whose `θ`-th power is
again a positive rational; that is, `v` lies in the group `K` of the log-product section.

This is the denominator-clearing step that identifies `U` with the `ℚ`-span of `log K`. -/
theorem exists_nat_mul_eq_log_of_thetaPullback {w : ℝ}
    (hw : InPrimeLogSpan w) (hThetaw : InPrimeLogSpan (logThreeDivLogTwo * w)) :
    ∃ K : ℕ, 0 < K ∧ ∃ v u : ℚ, 0 < v ∧ 0 < u ∧
      (K : ℝ) * w = Real.log ((v : ℚ) : ℝ) ∧
      ((v : ℚ) : ℝ) ^ logThreeDivLogTwo = ((u : ℚ) : ℝ) := by
  obtain ⟨N, hNpos, v₀, hv₀pos, hv₀⟩ := exists_nat_mul_eq_log_ratCast hw
  obtain ⟨M, hMpos, u₀, hu₀pos, hu₀⟩ := exists_nat_mul_eq_log_ratCast hThetaw
  have hVpos : (0 : ℚ) < v₀ ^ M := pow_pos hv₀pos M
  have hUpos : (0 : ℚ) < u₀ ^ N := pow_pos hu₀pos N
  have hVposR : (0 : ℝ) < ((v₀ ^ M : ℚ) : ℝ) := by exact_mod_cast hVpos
  have hUposR : (0 : ℝ) < ((u₀ ^ N : ℚ) : ℝ) := by exact_mod_cast hUpos
  have hlogV : Real.log ((v₀ ^ M : ℚ) : ℝ) = ((N * M : ℕ) : ℝ) * w := by
    have hcast : ((v₀ ^ M : ℚ) : ℝ) = ((v₀ : ℚ) : ℝ) ^ M := Rat.cast_pow v₀ M
    rw [hcast, Real.log_pow, ← hv₀]
    push_cast
    ring
  have hlogU : Real.log ((u₀ ^ N : ℚ) : ℝ) =
      logThreeDivLogTwo * (((N * M : ℕ) : ℝ) * w) := by
    have hcast : ((u₀ ^ N : ℚ) : ℝ) = ((u₀ : ℚ) : ℝ) ^ N := Rat.cast_pow u₀ N
    rw [hcast, Real.log_pow, ← hu₀]
    push_cast
    ring
  refine ⟨N * M, Nat.mul_pos hNpos hMpos, v₀ ^ M, u₀ ^ N, hVpos, hUpos, hlogV.symm, ?_⟩
  have hkey : Real.log ((v₀ ^ M : ℚ) : ℝ) * logThreeDivLogTwo =
      Real.log ((u₀ ^ N : ℚ) : ℝ) := by
    rw [hlogV, hlogU]
    ring
  rw [Real.rpow_def_of_pos hVposR, hkey, Real.exp_log hUposR]

/-! ### A rational exponent with a rational power of two is an integer -/

private theorem integer_of_rat_of_two_rpow_rat_of_nonneg {x : ℝ} (hx0 : 0 ≤ x)
    (hxrat : x ∈ Set.range ((↑) : ℚ → ℝ))
    (h₂ : ∃ r : ℚ, ((r : ℚ) : ℝ) = (2 : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨q, hq⟩ := hxrat
  obtain ⟨r, hr⟩ := h₂
  have hqR : (0 : ℝ) ≤ ((q : ℚ) : ℝ) := by
    rw [hq]
    exact hx0
  have hq0 : 0 ≤ q := by exact_mod_cast hqR
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = q.num :=
    ⟨q.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0)⟩
  have hd0 : ((q.den : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hxd : x * ((q.den : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
    have hcast : ((q : ℚ) : ℝ) * ((q.den : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
      rw [Rat.cast_def, div_mul_cancel₀ _ hd0]
    rw [← hq, hcast]
    exact_mod_cast hn.symm
  have hrpow : ((r : ℚ) : ℝ) ^ q.den = (((2 ^ n : ℕ) : ℤ) : ℝ) := by
    have h1 : ((r : ℚ) : ℝ) ^ q.den = ((2 : ℝ) ^ x) ^ (q.den : ℕ) := by rw [hr]
    have h2 : ((2 : ℝ) ^ x) ^ (q.den : ℕ) = (2 : ℝ) ^ (x * ((q.den : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ x) q.den,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h1, h2, hxd, Real.rpow_natCast]
    norm_cast
  have hrint : ∃ y : ℤ, ((r : ℚ) : ℝ) = (y : ℝ) := by
    by_contra hcon
    exact (Rat.not_irrational r)
      (irrational_nrt_of_notint_nrt q.den ((2 ^ n : ℕ) : ℤ) hrpow hcon q.pos)
  obtain ⟨y, hy⟩ := hrint
  exact IntegerExponent.integer_of_rational_of_two_rpow_integer ⟨q, hq⟩ ⟨y, hy.symm.trans hr⟩

/-- A rational exponent whose power of two is merely rational is already an integer.  This is
the step that upgrades rank one for the group `K` to the exact equality `K = ⟨2⟩`. -/
theorem integer_of_rat_of_two_rpow_rat {x : ℝ}
    (hxrat : x ∈ Set.range ((↑) : ℚ → ℝ))
    (h₂ : ∃ r : ℚ, ((r : ℚ) : ℝ) = (2 : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  rcases le_or_gt 0 x with hx0 | hx0
  · exact integer_of_rat_of_two_rpow_rat_of_nonneg hx0 hxrat h₂
  · obtain ⟨q, hq⟩ := hxrat
    obtain ⟨r, hr⟩ := h₂
    have hnegrat : ((-q : ℚ) : ℝ) = -x := by
      push_cast
      rw [hq]
    have h2neg : ((r⁻¹ : ℚ) : ℝ) = (2 : ℝ) ^ (-x) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← hr, Rat.cast_inv]
    obtain ⟨m, hm⟩ :=
      integer_of_rat_of_two_rpow_rat_of_nonneg (x := -x) (by linarith) ⟨-q, hnegrat⟩
        ⟨r⁻¹, h2neg⟩
    refine ⟨-m, ?_⟩
    push_cast
    linarith [hm]

/-! ### The equivalence -/

/-- **Operator form implies the rational-output form.**  If `θ` carries only the line
`ℚ * log 2` back into `W`, then rationality of `2 ^ x` and `3 ^ x` forces `x` to be an
integer. -/
theorem rationalOutput_of_primeLogSpanThetaPullbackRankOne
    (h : PrimeLogSpanThetaPullbackRankOne) : RationalOutputTwoBaseConjecture := by
  intro x h₂ h₃
  obtain ⟨qM, hqM⟩ := h₂
  obtain ⟨qA, hqA⟩ := h₃
  have hqMR : (0 : ℝ) < ((qM : ℚ) : ℝ) := by
    rw [hqM]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hqAR : (0 : ℝ) < ((qA : ℚ) : ℝ) := by
    rw [hqA]
    exact Real.rpow_pos_of_pos (by norm_num) x
  have hqMpos : 0 < qM := by exact_mod_cast hqMR
  have hqApos : 0 < qA := by exact_mod_cast hqAR
  have hlogM : Real.log ((qM : ℚ) : ℝ) = x * Real.log 2 := by
    rw [hqM, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hlogA : Real.log ((qA : ℚ) : ℝ) = x * Real.log 3 := by
    rw [hqA, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  have hspan : InPrimeLogSpan (x * Real.log 2) := by
    rw [← hlogM]
    exact inPrimeLogSpan_log_ratCast hqMpos
  have hspanTheta : InPrimeLogSpan (logThreeDivLogTwo * (x * Real.log 2)) := by
    have hEq : logThreeDivLogTwo * (x * Real.log 2) = Real.log ((qA : ℚ) : ℝ) := by
      rw [hlogA, ← theta_mul_logTwo]
      ring
    rw [hEq]
    exact inPrimeLogSpan_log_ratCast hqApos
  obtain ⟨q, hq⟩ := h (x * Real.log 2) hspan hspanTheta
  have hxq : x = (q : ℝ) := mul_right_cancel₀ logTwo_ne_zero hq
  exact integer_of_rat_of_two_rpow_rat ⟨q, hxq.symm⟩ ⟨qM, hqM⟩

/-- **Rational-output form implies the operator form.**  If rationality of both powers forces
an integral exponent, then `θ` carries only the line `ℚ * log 2` back into `W`. -/
theorem primeLogSpanThetaPullbackRankOne_of_rationalOutput
    (h : RationalOutputTwoBaseConjecture) : PrimeLogSpanThetaPullbackRankOne := by
  intro w hw hThetaw
  obtain ⟨K, hKpos, v, u, hvpos, _hupos, hKw, hvu⟩ :=
    exists_nat_mul_eq_log_of_thetaPullback hw hThetaw
  have hvposR : (0 : ℝ) < ((v : ℚ) : ℝ) := by exact_mod_cast hvpos
  obtain ⟨y, hy2⟩ : ∃ y : ℝ, y * Real.log 2 = Real.log ((v : ℚ) : ℝ) :=
    ⟨Real.log ((v : ℚ) : ℝ) / Real.log 2, div_mul_cancel₀ _ logTwo_ne_zero⟩
  have h2y : ((v : ℚ) : ℝ) = (2 : ℝ) ^ y := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2) y, hy2]
    exact (Real.exp_log hvposR).symm
  have h3y : ((u : ℚ) : ℝ) = (3 : ℝ) ^ y := by
    have hstep : Real.log 3 * y = Real.log ((v : ℚ) : ℝ) * logThreeDivLogTwo := by
      rw [← theta_mul_logTwo, ← hy2]
      ring
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), hstep,
      ← Real.rpow_def_of_pos hvposR, hvu]
  obtain ⟨n, hn⟩ := h y ⟨v, h2y⟩ ⟨u, h3y⟩
  have hKlog : ((K : ℕ) : ℝ) * w = ((n : ℤ) : ℝ) * Real.log 2 := by
    rw [hKw, ← hy2, hn]
  have hKR : ((K : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hKpos.ne'
  refine ⟨((n : ℤ) : ℚ) / ((K : ℕ) : ℚ), ?_⟩
  have hgoal : ((((n : ℤ) : ℚ) / ((K : ℕ) : ℚ) : ℚ) : ℝ) * Real.log 2 =
      (((n : ℤ) : ℝ) * Real.log 2) / ((K : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hgoal, ← hKlog, mul_comm ((K : ℕ) : ℝ) w, mul_div_assoc, div_self hKR, mul_one]

/-- **Operator form of the two-base conjecture.**  With `W` the `ℚ`-span of the prime
logarithms and `U = {w ∈ W : θ * w ∈ W}`, the statement `dim_ℚ U = 1` --- in the elementary
form that `U` is contained in the line `ℚ * log 2` --- is equivalent to the rational-output
form of the conjecture.

Both sides are open; only the biconditional is proved here. -/
theorem primeLogSpanThetaPullbackRankOne_iff_rationalOutput :
    PrimeLogSpanThetaPullbackRankOne ↔ RationalOutputTwoBaseConjecture :=
  ⟨rationalOutput_of_primeLogSpanThetaPullbackRankOne,
    primeLogSpanThetaPullbackRankOne_of_rationalOutput⟩

/-- The rational-output form implies the Alaoglu--Erdős conjecture. -/
theorem alaogluErdosConjecture_of_rationalOutput
    (h : RationalOutputTwoBaseConjecture) : AlaogluErdosConjecture := by
  intro x h₂ h₃
  obtain ⟨zM, hzM⟩ := h₂
  obtain ⟨zA, hzA⟩ := h₃
  refine h x ⟨(zM : ℚ), ?_⟩ ⟨(zA : ℚ), ?_⟩
  · exact_mod_cast hzM
  · exact_mod_cast hzA

/-- **The operator form implies the Alaoglu--Erdős conjecture.**  A proof that `θ` returns only
the line `ℚ * log 2` into `W` would settle the conjecture. -/
theorem alaogluErdosConjecture_of_primeLogSpanThetaPullbackRankOne
    (h : PrimeLogSpanThetaPullbackRankOne) : AlaogluErdosConjecture :=
  alaogluErdosConjecture_of_rationalOutput
    (rationalOutput_of_primeLogSpanThetaPullbackRankOne h)

end LeanProofs.TwoBaseIntegerExponent
