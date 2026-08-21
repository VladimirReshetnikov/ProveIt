import ExponentialIdentities.TwoBaseIntegerExponent.OddCore
import ExponentialIdentities.TwoBaseIntegerExponent.LeastSolution
import ExponentialIdentities.TwoBaseIntegerExponent.ThreeDenominatorNormalization

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-! ### The rational-power index of a nonzero real number -/

/-- The integer exponents at which a fixed nonzero real number has rational value. -/
def rationalPowerIndices (E : ℝ) (hE : E ≠ 0) : AddSubgroup ℤ where
  carrier := {j : ℤ | E ^ j ∈ Set.range ((↑) : ℚ → ℝ)}
  zero_mem' := ⟨1, by norm_num⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := ha
    obtain ⟨r, hr⟩ := hb
    refine ⟨q * r, ?_⟩
    push_cast
    rw [zpow_add₀ hE, ← hq, ← hr]
  neg_mem' := by
    intro a ha
    obtain ⟨q, hq⟩ := ha
    refine ⟨q⁻¹, ?_⟩
    push_cast
    rw [zpow_neg, ← hq]

@[simp] theorem mem_rationalPowerIndices_iff {E : ℝ} {hE : E ≠ 0} {j : ℤ} :
    j ∈ rationalPowerIndices E hE ↔ E ^ j ∈ Set.range ((↑) : ℚ → ℝ) := Iff.rfl

/-- Every nonzero additive subgroup of `ℤ` has a least positive natural generator. -/
theorem AddSubgroup.Int.exists_least_positive_generator
    (H : AddSubgroup ℤ) (hH : H ≠ ⊥) :
    ∃ d : ℕ, 0 < d ∧ H = AddSubgroup.zmultiples (d : ℤ) ∧
      (d : ℤ) ∈ H ∧
      ∀ j : ℤ, j ∈ H → 0 < j → (d : ℤ) ≤ j := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic H
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    apply hH
    exact ha.trans AddSubgroup.closure_singleton_zero
  let d : ℕ := a.natAbs
  have hd : 0 < d := Int.natAbs_pos.mpr ha0
  have hgen : H = AddSubgroup.zmultiples (d : ℤ) := by
    calc
      H = AddSubgroup.closure {a} := ha
      _ = AddSubgroup.zmultiples a := (AddSubgroup.zmultiples_eq_closure a).symm
      _ = AddSubgroup.zmultiples (d : ℤ) := (Int.zmultiples_natAbs a).symm
  refine ⟨d, hd, hgen, ?_, ?_⟩
  · rw [hgen, Int.mem_zmultiples_iff]
  · intro j hj hjpos
    rw [hgen, Int.mem_zmultiples_iff] at hj
    obtain ⟨c, rfl⟩ := hj
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    have hc : 0 < c := by
      by_contra hc0
      have hc_nonpos : c ≤ 0 := Int.not_lt.mp hc0
      have : (d : ℤ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdZ.le hc_nonpos
      omega
    calc
      (d : ℤ) = (d : ℤ) * 1 := by ring
      _ ≤ (d : ℤ) * c := mul_le_mul_of_nonneg_left (by omega) hdZ.le

/-- If one nonzero power of `E` is rational, all rational powers of `E` occur exactly at
the multiples of a least positive index `d`. -/
theorem exists_rationalPowerIndex {E : ℝ} (hE : E ≠ 0)
    {j₀ : ℤ} (hj₀ : j₀ ≠ 0) (hrat : E ^ j₀ ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ d : ℕ, 0 < d ∧
      rationalPowerIndices E hE = AddSubgroup.zmultiples (d : ℤ) ∧
      E ^ (d : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) ∧
      (∀ j : ℤ, E ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔ (d : ℤ) ∣ j) ∧
      ∀ j : ℤ, E ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
        0 < j → (d : ℤ) ≤ j := by
  have hne : rationalPowerIndices E hE ≠ ⊥ := by
    intro hbot
    have hjmem : j₀ ∈ rationalPowerIndices E hE := hrat
    have : j₀ ∈ (⊥ : AddSubgroup ℤ) := by simpa [hbot] using hjmem
    exact hj₀ (by simpa using this)
  obtain ⟨d, hd, hgen, hdmem, hleast⟩ :=
    AddSubgroup.Int.exists_least_positive_generator (rationalPowerIndices E hE) hne
  refine ⟨d, hd, hgen, hdmem, fun j ↦ ?_, ?_⟩
  · rw [← mem_rationalPowerIndices_iff (hE := hE), hgen, Int.mem_zmultiples_iff]
  · intro j hj hjpos
    exact hleast j hj hjpos

/-! ### Application to a fixed common odd core -/

/-- The irrational power attached to the common odd core. -/
def oddCoreRpow (w : ℕ) : ℝ := (w : ℝ) ^ logThreeDivLogTwo

theorem oddCoreRpow_pos {w : ℕ} (hw : 0 < w) : 0 < oddCoreRpow w :=
  Real.rpow_pos_of_pos (by exact_mod_cast hw) _

/-- The logarithmic coordinate associated to a common-odd-core representation. -/
theorem twoBaseCandidateExponent_eq_add_mul_logb_of_oddCore_rep
    {w i j m : ℕ} (hw : 0 < w) (hrep : m = 2 ^ i * w ^ j) :
    twoBaseCandidateExponent m = i + j * Real.logb 2 w := by
  rw [twoBaseCandidateExponent, hrep]
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  push_cast
  rw [Real.logb_mul (pow_ne_zero i (by norm_num)) (pow_ne_zero j hwR),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

private theorem two_rpow_logThreeDivLogTwo :
    (2 : ℝ) ^ logThreeDivLogTwo = 3 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logThreeDivLogTwo]
  have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
      Real.log (3 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- In common-odd-core coordinates, the second integral power is `3 ^ i * E ^ j`. -/
theorem candidateRpow_eq_three_pow_mul_oddCoreRpow_pow
    {w i j m : ℕ} (hm : m = 2 ^ i * w ^ j) :
    (m : ℝ) ^ logThreeDivLogTwo =
      (3 : ℝ) ^ i * oddCoreRpow w ^ j := by
  subst m
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) logThreeDivLogTwo i,
    ← Real.rpow_pow_comm (Nat.cast_nonneg w) logThreeDivLogTwo j,
    two_rpow_logThreeDivLogTwo]
  rfl

/-- The odd-core exponent of every candidate is a rational-power index of `E`. -/
theorem oddCoreRpow_pow_rational_of_candidate
    {w i j m : ℕ} (hm : TwoBaseNaturalCandidate m)
    (hrep : m = 2 ^ i * w ^ j) :
    oddCoreRpow w ^ (j : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨z, hz⟩ := hm.2
  refine ⟨(z : ℚ) / (3 : ℚ) ^ i, ?_⟩
  push_cast
  rw [zpow_natCast]
  rw [div_eq_iff (pow_ne_zero i (by norm_num : (3 : ℝ) ≠ 0))]
  rw [mul_comm]
  exact hz.trans (candidateRpow_eq_three_pow_mul_oddCoreRpow_pow hrep)

/-! ### The normalized denominator calculation -/

/-- If `c` is positive and either `a = 0` or `c` is prime to `3`, then the rational number
`3 ^ i * (c / 3 ^ a) ^ k` is an integer exactly when `a * k ≤ i`.

This is the arithmetic step which turns the rational-power index into an exact additive
monoid generator. -/
theorem three_pow_mul_normalized_pow_integer_iff
    {a c i k : ℕ} (hc : 0 < c) (ha : a = 0 ∨ ¬ 3 ∣ c) :
    (3 : ℝ) ^ i * ((c : ℝ) / (3 : ℝ) ^ a) ^ k ∈
        Set.range ((↑) : ℤ → ℝ) ↔
      a * k ≤ i := by
  rcases ha with rfl | hc3
  · constructor
    · intro
      simp
    · intro
      refine ⟨(3 ^ i * c ^ k : ℕ), ?_⟩
      push_cast
      simp
  constructor
  · rintro ⟨z, hz⟩
    have hzposR : (0 : ℝ) < z := by
      rw [hz]
      positivity
    have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
    obtain ⟨z₀, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
    change (0 : ℝ) < z₀ at hzposR
    change (z₀ : ℝ) = (3 : ℝ) ^ i * ((c : ℝ) / (3 : ℝ) ^ a) ^ k at hz
    have hz₀pos : 0 < z₀ := by exact_mod_cast hzposR
    have hclearR :
        (z₀ : ℝ) * (3 : ℝ) ^ (a * k) =
          (3 : ℝ) ^ i * (c : ℝ) ^ k := by
      rw [hz, div_pow, ← pow_mul]
      field_simp
    have hclearN : z₀ * 3 ^ (a * k) = 3 ^ i * c ^ k := by
      exact_mod_cast hclearR
    have hfac := congrArg (fun n : ℕ ↦ n.factorization 3) hclearN
    rw [Nat.factorization_mul hz₀pos.ne' (pow_ne_zero _ (by norm_num)),
      Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hc.ne'),
      Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow] at hfac
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hfac
    rw [(by norm_num : Nat.Prime 3).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hc3] at hfac
    have hfac' : z₀.factorization 3 + a * k = i := by
      simpa using hfac
    exact (Nat.le_add_left (a * k) (z₀.factorization 3)).trans_eq hfac'
  · intro hle
    refine ⟨(3 ^ (i - a * k) * c ^ k : ℕ), ?_⟩
    push_cast
    rw [div_pow, ← pow_mul, pow_sub₀ (3 : ℝ) (by norm_num) hle]
    field_simp

/-- Once the primitive odd-core power is normalized as `c / 3 ^ a`, the candidate
condition in coordinates is the single linear inequality `a * k ≤ i`. -/
theorem twoBaseNaturalCandidate_primitive_coordinates_iff
    {w d a c i k : ℕ} (hw : 0 < w) (hc : 0 < c)
    (ha : a = 0 ∨ ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a) :
    TwoBaseNaturalCandidate (2 ^ i * w ^ (d * k)) ↔ a * k ≤ i := by
  constructor
  · intro hm
    have hint := hm.2
    rw [candidateRpow_eq_three_pow_mul_oddCoreRpow_pow (m := 2 ^ i * w ^ (d * k)) rfl,
      pow_mul, hnorm] at hint
    exact (three_pow_mul_normalized_pow_integer_iff hc ha).mp hint
  · intro hle
    refine ⟨by positivity, ?_⟩
    rw [candidateRpow_eq_three_pow_mul_oddCoreRpow_pow (m := 2 ^ i * w ^ (d * k)) rfl,
      pow_mul, hnorm]
    exact (three_pow_mul_normalized_pow_integer_iff hc ha).mpr hle

/-- Conditional on a fixed common odd core and a counterexample, the allowed odd-core
exponents are all divisible by one least positive integer `d`. -/
theorem exists_primitive_oddCore_index
    {w : ℕ} (hw : 1 < w)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hfail : ∃ m : ℕ, TwoBaseNaturalCandidate m ∧
      ¬ ∃ n : ℕ, m = 2 ^ n) :
    ∃ d : ℕ, 0 < d ∧
      rationalPowerIndices (oddCoreRpow w) (oddCoreRpow_pos (by omega)).ne' =
        AddSubgroup.zmultiples (d : ℤ) ∧
      oddCoreRpow w ^ (d : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) ∧
      (∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔
        (d : ℤ) ∣ j) ∧
      (∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
        0 < j → (d : ℤ) ≤ j) ∧
      ∀ m i j : ℕ, TwoBaseNaturalCandidate m →
        m = 2 ^ i * w ^ j → d ∣ j := by
  obtain ⟨m₀, hm₀, hm₀pow⟩ := hfail
  obtain ⟨i₀, j₀, hrep₀⟩ := hrep m₀ hm₀
  have hj₀ : 0 < j₀ := by
    rcases j₀.eq_zero_or_pos with h | h
    · subst j₀
      simp only [pow_zero, mul_one] at hrep₀
      exact (hm₀pow ⟨i₀, hrep₀⟩).elim
    · exact h
  have hE : oddCoreRpow w ≠ 0 := (oddCoreRpow_pos (by omega)).ne'
  have hrat₀ : oddCoreRpow w ^ (j₀ : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) :=
    oddCoreRpow_pow_rational_of_candidate hm₀ hrep₀
  obtain ⟨d, hd, hgroup, hdRat, hiff, hleast⟩ :=
    exists_rationalPowerIndex hE (by exact_mod_cast hj₀.ne') hrat₀
  refine ⟨d, hd, hgroup, hdRat, hiff, hleast, ?_⟩
  intro m i j hm hij
  have hrat : oddCoreRpow w ^ (j : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) :=
    oddCoreRpow_pow_rational_of_candidate hm hij
  exact_mod_cast (hiff (j : ℤ)).mp hrat

/-- Every two-base solution lies in the rank-two additive monoid generated by `1` and
`d * logb 2 w`, where `d` is the primitive rational-power index of the common odd core. -/
theorem exists_solution_submonoid_generator_of_fixed_oddCore
    {w : ℕ} (hw : 1 < w)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hfail : ∃ m : ℕ, TwoBaseNaturalCandidate m ∧
      ¬ ∃ n : ℕ, m = 2 ^ n) :
    ∃ d : ℕ, 0 < d ∧
      ∀ x : ℝ,
        (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
        (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
        ∃ i k : ℕ, x = i + k * ((d : ℝ) * Real.logb 2 w) := by
  obtain ⟨d, hd, _, _, _, _, hdiv⟩ := exists_primitive_oddCore_index hw hrep hfail
  refine ⟨d, hd, ?_⟩
  intro x h₂ h₃
  obtain ⟨m, _, hm, hx⟩ := exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
  obtain ⟨i, j, hij⟩ := hrep m hm
  obtain ⟨k, hk⟩ := hdiv m i j hm hij
  refine ⟨i, k, ?_⟩
  rw [hx, twoBaseCandidateExponent, hij]
  have hwR : (w : ℝ) ≠ 0 := by positivity
  push_cast
  rw [Real.logb_mul (pow_ne_zero i (by norm_num)) (pow_ne_zero j hwR),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  rw [hk]
  push_cast
  ring

/-- **Exact conditional solution monoid.**  Suppose `d` is the rational-power index of a
fixed common odd core and its primitive rational power has the normalized form
`E ^ d = c / 3 ^ a`, with the numerator prime to `3` whenever the denominator is nontrivial.
Then the full two-base solution set is exactly the additive monoid generated by `1` and
`a + d * logb 2 w`. -/
theorem twoBaseIntegralSolution_iff_exists_primitive_coordinates
    {w d a c : ℕ} (hw : 1 < w) (_hd : 0 < d)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hindex : ∀ j : ℤ,
      oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔ (d : ℤ) ∣ j)
    (hc : 0 < c) (ha : a = 0 ∨ ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (x : ℝ) :
    TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = n + k * ((a : ℝ) + d * Real.logb 2 w) := by
  constructor
  · rintro ⟨h₂, h₃⟩
    obtain ⟨m, _, hm, hx⟩ :=
      exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
    obtain ⟨i, j, hij⟩ := hrep m hm
    have hjRat : oddCoreRpow w ^ (j : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) :=
      oddCoreRpow_pow_rational_of_candidate hm hij
    have hdj : d ∣ j := by
      exact_mod_cast (hindex (j : ℤ)).mp hjRat
    obtain ⟨k, rfl⟩ := hdj
    have hint := hm.2
    rw [candidateRpow_eq_three_pow_mul_oddCoreRpow_pow hij, pow_mul, hnorm] at hint
    have hai : a * k ≤ i :=
      (three_pow_mul_normalized_pow_integer_iff hc ha).mp hint
    refine ⟨i - a * k, k, ?_⟩
    rw [hx, twoBaseCandidateExponent_eq_add_mul_logb_of_oddCore_rep (by omega) hij]
    have hiR : (i : ℝ) = ((i - a * k : ℕ) : ℝ) + (a * k : ℕ) := by
      exact_mod_cast (Nat.sub_add_cancel hai).symm
    rw [hiR]
    push_cast
    ring
  · rintro ⟨n, k, rfl⟩
    have hm : TwoBaseNaturalCandidate (2 ^ (n + a * k) * w ^ (d * k)) :=
      (twoBaseNaturalCandidate_primitive_coordinates_iff (by omega) hc ha hnorm).mpr
        (Nat.le_add_left (a * k) n)
    have hp := hm.integer_powers
    have hexp :
        twoBaseCandidateExponent (2 ^ (n + a * k) * w ^ (d * k)) =
          (n : ℝ) + k * ((a : ℝ) + d * Real.logb 2 w) := by
      rw [twoBaseCandidateExponent_eq_add_mul_logb_of_oddCore_rep (by omega) rfl]
      push_cast
      ring
    rwa [hexp] at hp

/-- For an odd common core, the primitive generator from the exact monoid theorem is itself
the least noninteger two-base solution. -/
theorem isLeastTwoBaseNonintegerSolution_primitive_generator
    {w d a c : ℕ} (hodd : Odd w) (hw : 1 < w) (hd : 0 < d)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hindex : ∀ j : ℤ,
      oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔ (d : ℤ) ∣ j)
    (hc : 0 < c) (ha : a = 0 ∨ ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a) :
    IsLeastTwoBaseNonintegerSolution
      ((a : ℝ) + d * Real.logb 2 w) := by
  let β : ℝ := (a : ℝ) + d * Real.logb 2 w
  have hchar (x : ℝ) : TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = n + k * β := by
    simpa only [β] using twoBaseIntegralSolution_iff_exists_primitive_coordinates
      hw hd hrep hindex hc ha hnorm x
  have hβsol : TwoBaseIntegralSolution β :=
    (hchar β).mpr ⟨0, 1, by simp⟩
  have hlogpos : 0 < Real.logb 2 (w : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hw)
  have hβpos : 0 < β := by
    dsimp only [β]
    positivity
  have hm : TwoBaseNaturalCandidate (2 ^ a * w ^ d) := by
    simpa using
      (twoBaseNaturalCandidate_primitive_coordinates_iff (w := w) (d := d)
        (a := a) (c := c) (i := a) (k := 1) (by omega) hc ha hnorm).mpr (by simp)
  have hexp : twoBaseCandidateExponent (2 ^ a * w ^ d) = β := by
    rw [twoBaseCandidateExponent_eq_add_mul_logb_of_oddCore_rep (by omega) rfl]
  have hβnonint : β ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    have hzposR : (0 : ℝ) < z := by rw [hz]; exact hβpos
    have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hzpos.le
    change (r : ℝ) = β at hz
    have hpowR : ((2 ^ a * w ^ d : ℕ) : ℝ) = ((2 ^ r : ℕ) : ℝ) := by
      calc
        ((2 ^ a * w ^ d : ℕ) : ℝ) =
            (2 : ℝ) ^ twoBaseCandidateExponent (2 ^ a * w ^ d) :=
          (two_rpow_twoBaseCandidateExponent hm.1).symm
        _ = (2 : ℝ) ^ β := by rw [hexp]
        _ = (2 : ℝ) ^ (r : ℝ) := by rw [hz]
        _ = ((2 ^ r : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    have hpowN : 2 ^ a * w ^ d = 2 ^ r := by exact_mod_cast hpowR
    have hoc := congrArg (fun n : ℕ ↦ ordCompl[2] n) hpowN
    rw [Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two
        (show Odd (w ^ d) from hodd.pow).not_two_dvd_nat,
      Nat.ordCompl_self_pow Nat.prime_two] at hoc
    have hwpow : 1 < w ^ d := (one_lt_pow_iff hd.ne').mpr hw
    omega
  refine ⟨⟨hβsol, hβnonint⟩, ?_⟩
  intro x hx
  obtain ⟨n, k, hxrep⟩ := (hchar x).mp hx.1
  have hk : 0 < k := by
    rcases k.eq_zero_or_pos with rfl | hk
    · apply (hx.2 ⟨(n : ℤ), ?_⟩).elim
      simpa using hxrep.symm
    · exact hk
  rw [hxrep]
  have hmul : β ≤ (k : ℝ) * β := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  exact hmul.trans (le_add_of_nonneg_left (Nat.cast_nonneg n))

/-- Packaged form: failure together with a fixed common odd core produces a least rational-power
index `d`; every normalized expression for its primitive power then gives the exact solution
monoid generated by `1` and `a + d * logb 2 w`. -/
theorem exists_primitive_index_with_exact_solution_monoid
    {w : ℕ} (hw : 1 < w)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hfail : ∃ m : ℕ, TwoBaseNaturalCandidate m ∧
      ¬ ∃ n : ℕ, m = 2 ^ n) :
    ∃ d : ℕ, 0 < d ∧
      (∀ j : ℤ,
        oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔ (d : ℤ) ∣ j) ∧
      ∀ a c : ℕ, 0 < c → (a = 0 ∨ ¬ 3 ∣ c) →
        oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a →
        ∀ x : ℝ, TwoBaseIntegralSolution x ↔
          ∃ n k : ℕ, x = n + k * ((a : ℝ) + d * Real.logb 2 w) := by
  obtain ⟨d, hd, _, _, hindex, _, _⟩ := exists_primitive_oddCore_index hw hrep hfail
  refine ⟨d, hd, hindex, ?_⟩
  intro a c hc ha hnorm x
  exact twoBaseIntegralSolution_iff_exists_primitive_coordinates
    hw hd hrep hindex hc ha hnorm x

/-- **Canonical conditional classification.**  For a fixed odd common core, failure of the
two-base conjecture automatically supplies a least rational-power index `d`, a normalized
primitive power `E ^ d = c / 3 ^ a`, the exact solution monoid generated by
`1` and `β = a + d * logb 2 w`, and `β` as the least noninteger solution. -/
theorem exists_exact_solution_monoid_of_fixed_common_oddCore
    {w : ℕ} (hodd : Odd w) (hw : 1 < w)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hfail : ∃ m : ℕ, TwoBaseNaturalCandidate m ∧
      ¬ ∃ n : ℕ, m = 2 ^ n) :
    ∃ d a c : ℕ,
      0 < d ∧ 0 < c ∧ (a = 0 ∨ ¬ 3 ∣ c) ∧
      (∀ j : ℤ,
        oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔ (d : ℤ) ∣ j) ∧
      (∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
        0 < j → (d : ℤ) ≤ j) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      (∀ x : ℝ, TwoBaseIntegralSolution x ↔
        ∃ n k : ℕ, x = n + k * ((a : ℝ) + d * Real.logb 2 w)) ∧
      IsLeastTwoBaseNonintegerSolution ((a : ℝ) + d * Real.logb 2 w) := by
  obtain ⟨d, hd, _, hdRat, hindex, hleast, hdiv⟩ :=
    exists_primitive_oddCore_index hw hrep hfail
  obtain ⟨m, hm, hmPow⟩ := hfail
  obtain ⟨i, j, hij⟩ := hrep m hm
  have hj : 0 < j := by
    rcases j.eq_zero_or_pos with rfl | hj
    · simp only [pow_zero, mul_one] at hij
      exact (hmPow ⟨i, hij⟩).elim
    · exact hj
  obtain ⟨k, rfl⟩ := hdiv m i j hm hij
  have hk : 0 < k := by
    rcases k.eq_zero_or_pos with rfl | hk
    · simp at hj
    · exact hk
  have hq : oddCoreRpow w ^ d ∈ Set.range ((↑) : ℚ → ℝ) := by
    simpa using hdRat
  have hint : (3 : ℝ) ^ i * (oddCoreRpow w ^ d) ^ k ∈
      Set.range ((↑) : ℤ → ℝ) := by
    have hint' := hm.2
    rw [candidateRpow_eq_three_pow_mul_oddCoreRpow_pow hij, pow_mul] at hint'
    exact hint'
  obtain ⟨a, c, hc, ha, hnorm⟩ :=
    exists_three_pow_denominator_of_rational_power
      (oddCoreRpow_pos (by omega)) hd hk hq hint
  refine ⟨d, a, c, hd, hc, ha, hindex, hleast, hnorm, ?_, ?_⟩
  · intro x
    exact twoBaseIntegralSolution_iff_exists_primitive_coordinates
      hw hd hrep hindex hc ha hnorm x
  · exact isLeastTwoBaseNonintegerSolution_primitive_generator
      hodd hw hd hrep hindex hc ha hnorm

end

end LeanProofs.TwoBaseIntegerExponent
