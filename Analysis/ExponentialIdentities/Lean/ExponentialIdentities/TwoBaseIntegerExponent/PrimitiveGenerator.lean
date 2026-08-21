import ExponentialIdentities.TwoBaseIntegerExponent.Localization
import ExponentialIdentities.TwoBaseIntegerExponent.OddCore

/-!
# The exact primitive-generator theorem

Conditional on the failure of the Alaoglu--Erd\H{o}s conjecture, this file proves the
strongest structural rigidity statement in the corpus: there is a least nonintegral
solution `β`, with `2 ^ β` and `3 ^ β` natural numbers, such that the *entire* solution
set of the two integrality conditions is exactly
\[
  \{\, n + k\,β : n, k \in ℕ \,\},
\]
with unique representations.  In particular the solution set is the free additive monoid on
`1` and one irrational generator: there is no residual "exponent semigroup" freedom.

Construction: take the kernel-verified common odd core `w` (`OddCore`), set
`E = w ^ (log 3 / log 2)`, let `d ≥ 1` be least with `E ^ d ∈ ℚ` (it exists because some
candidate is not a power of two), clear the denominator of `E ^ d` --- which can only
involve the prime `3` --- as `E ^ d = A / 3 ^ a` in lowest terms, and put
`β = a + d·log₂ w`.  Minimality of `d` forces every occurring odd-core exponent to be a
multiple of `d`, and reducedness forces the accompanying power of two to clear the
denominator, which is exactly the linear threshold `i ≥ a·k`.

Everything here is unconditional Lean; the failure hypothesis enters only as the explicit
assumption `hex` of the main theorem.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- Splitting the `θ`-th power of `2 ^ i * w ^ j` into `3 ^ i` times powers of
`E = w ^ θ`. -/
theorem pow_mul_pow_rpow_theta (w i j : ℕ) (hw : 0 < w) :
    ((2 ^ i * w ^ j : ℕ) : ℝ) ^ logThreeDivLogTwo =
      (3 : ℝ) ^ i * ((w : ℝ) ^ logThreeDivLogTwo) ^ j := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  · rw [← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm ((i : ℝ)) logThreeDivLogTwo,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_logThreeDivLogTwo,
      Real.rpow_natCast]
  · rw [← Real.rpow_natCast (w : ℝ) j, ← Real.rpow_mul hwR.le,
      mul_comm ((j : ℝ)) logThreeDivLogTwo,
      Real.rpow_mul hwR.le, Real.rpow_natCast]

/-- `log₂ w` is irrational for odd `w > 1`. -/
theorem irrational_logb_two_of_odd {w : ℕ} (hodd : Odd w) (hw : 1 < w) :
    Irrational (Real.logb 2 w) := by
  intro hrat
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hpow : (2 : ℝ) ^ Real.logb 2 w = w :=
    Real.rpow_logb (by norm_num) (by norm_num) hwR
  have hint : Real.logb 2 w ∈ Set.range ((↑) : ℤ → ℝ) := by
    apply IntegerExponent.integer_of_rational_of_two_rpow_integer hrat
    exact ⟨(w : ℤ), by rw [hpow]; push_cast; ring⟩
  obtain ⟨z, hz⟩ := hint
  have hznn : 0 ≤ z := by
    have h1 : (1 : ℝ) < w := by exact_mod_cast hw
    have hpos : 0 < Real.logb 2 w := Real.logb_pos (by norm_num) h1
    exact_mod_cast le_of_lt (hz ▸ hpos)
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hznn
  have hwt : (w : ℝ) = ((2 ^ t : ℕ) : ℝ) := by
    rw [← hpow, ← hz]
    rw [show (((t : ℕ) : ℤ) : ℝ) = ((t : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    ring
  have hwt' : w = 2 ^ t := by exact_mod_cast hwt
  obtain ⟨s, hs⟩ := hodd
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [pow_zero] at hwt'
    omega
  · have h2w : 2 ∣ w := hwt' ▸ dvd_pow_self 2 ht.ne'
    obtain ⟨r, hr⟩ := h2w
    omega

/-- **Exact primitive-generator theorem.**  If a nonintegral two-base solution exists, then
there are an irrational `β` and naturals `M, A ≥ 2` with `2 ^ β = M` and `3 ^ β = A` such
that: the solutions of the two integrality conditions are exactly the numbers `n + k·β`
with `n, k : ℕ`; the representation is unique; and `β` bounds every nonintegral solution
from below (hence, being the solution `(n,k) = (0,1)`, it is the least one). -/
theorem exists_primitive_generator
    (hex : ∃ x : ℝ,
      (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) ∧
      x ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ β : ℝ, ∃ M A : ℕ, 1 < M ∧ 1 < A ∧
      (2 : ℝ) ^ β = M ∧ (3 : ℝ) ^ β = A ∧ Irrational β ∧
      (∀ y : ℝ,
        ((2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) ∧
         (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ)) ↔
        ∃ n k : ℕ, y = (n : ℝ) + (k : ℝ) * β) ∧
      (∀ n k n' k' : ℕ,
        (n : ℝ) + (k : ℝ) * β = (n' : ℝ) + (k' : ℝ) * β → n = n' ∧ k = k') ∧
      (∀ y : ℝ,
        (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
        (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
        y ∉ Set.range ((↑) : ℤ → ℝ) → β ≤ y) := by
  classical
  obtain ⟨w, hwodd, hw1, hwrep⟩ := exists_common_odd_core_split
  have hw0 : 0 < w := by omega
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  set α := Real.logb 2 w with hα
  have hαirr : Irrational α := irrational_logb_two_of_odd hwodd hw1
  have h2α : (2 : ℝ) ^ α = w := Real.rpow_logb (by norm_num) (by norm_num) hwR
  have hαpos : 0 < α := Real.logb_pos (by norm_num) (by exact_mod_cast hw1)
  set E := (w : ℝ) ^ logThreeDivLogTwo with hE
  have hEpos : 0 < E := Real.rpow_pos_of_pos hwR _
  -- Every solution decomposes through the odd core.
  have hsol_data : ∀ y : ℝ,
      (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
      (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
      ∃ i j : ℕ, y = (i : ℝ) + (j : ℝ) * α ∧
        (3 : ℝ) ^ i * E ^ j ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro y h₂ h₃
    obtain ⟨m, hm0, hm, hy⟩ :=
      exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    rcases hwrep m hm with ⟨t, rfl⟩ | ⟨i, j, hj0, hij⟩
    · refine ⟨t, 0, ?_, ?_⟩
      · have hyt : y = t := by
          rw [hy, twoBaseCandidateExponent]
          push_cast
          rw [Real.logb, Real.log_pow]
          field_simp
        rw [hyt]
        push_cast
        ring
      · have h3y := hm.2
        have hsplit := pow_mul_pow_rpow_theta w t 0 hw0
        rw [pow_zero, mul_one, pow_zero, mul_one] at hsplit
        rw [hsplit] at h3y
        simpa using h3y
    · refine ⟨i, j, ?_, ?_⟩
      · rw [hy, twoBaseCandidateExponent, hij]
        push_cast
        rw [Real.logb, Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, hα, Real.logb]
        field_simp
      · have h3y := hm.2
        rw [hij, pow_mul_pow_rpow_theta w i j hw0, ← hE] at h3y
        exact h3y
  -- Some positive power of `E` is rational.
  have hPex : ∃ j : ℕ, 0 < j ∧ ∃ q' : ℚ, (q' : ℝ) = E ^ j := by
    obtain ⟨x₀, hx₂, hx₃, hxni⟩ := hex
    obtain ⟨i, j, hxeq, hmem⟩ := hsol_data x₀ hx₂ hx₃
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd ⟨(i : ℤ), by rw [hxeq]; push_cast; ring⟩ hxni
    · obtain ⟨z, hz⟩ := hmem
      have h3i : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
      refine ⟨j, hj0, (z : ℚ) / 3 ^ i, ?_⟩
      push_cast
      rw [hz]
      field_simp
  obtain ⟨d, ⟨hd0, q, hq⟩, hdmin⟩ :
      ∃ d : ℕ, (0 < d ∧ ∃ q' : ℚ, (q' : ℝ) = E ^ d) ∧
        ∀ j, j < d → ¬(0 < j ∧ ∃ q' : ℚ, (q' : ℝ) = E ^ j) :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  have hqposR : (0 : ℝ) < (q : ℝ) := hq ▸ pow_pos hEpos d
  have hqpos : 0 < q := by exact_mod_cast hqposR
  -- Minimality upgrades to divisibility.
  have hdvd : ∀ j : ℕ, (∃ q' : ℚ, (q' : ℝ) = E ^ j) → d ∣ j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact dvd_zero d
    obtain ⟨q', hq'⟩ := hj
    by_cases hr : j % d = 0
    · exact Nat.dvd_of_mod_eq_zero hr
    · exfalso
      apply hdmin (j % d) (Nat.mod_lt j hd0)
      refine ⟨Nat.pos_of_ne_zero hr, q' / q ^ (j / d), ?_⟩
      have hqd : ((E ^ d) ^ (j / d)) ≠ 0 := by positivity
      push_cast
      rw [hq', hq, div_eq_iff hqd, ← pow_mul, ← pow_add]
      congr 1
      exact (Nat.mod_add_div j d).symm
  -- The denominator of `q = E ^ d` is a power of three.
  have hexist_jk : ∃ i k : ℕ, 0 < k ∧
      (3 : ℝ) ^ i * E ^ (d * k) ∈ Set.range ((↑) : ℤ → ℝ) := by
    obtain ⟨x₀, hx₂, hx₃, hxni⟩ := hex
    obtain ⟨i, j, hxeq, hmem⟩ := hsol_data x₀ hx₂ hx₃
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd ⟨(i : ℤ), by rw [hxeq]; push_cast; ring⟩ hxni
    · obtain ⟨k, hk⟩ := hdvd j (by
        obtain ⟨z, hz⟩ := hmem
        have h3i : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
        refine ⟨(z : ℚ) / 3 ^ i, ?_⟩
        push_cast
        rw [hz]
        field_simp)
      refine ⟨i, k, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · omega
        · exact hkpos
      · rw [← hk]
        exact hmem
  obtain ⟨i₀, k₀, hk₀, hmem₀⟩ := hexist_jk
  obtain ⟨z₀, hz₀⟩ := hmem₀
  have hz₀Q : (z₀ : ℚ) = 3 ^ i₀ * q ^ k₀ := by
    have hcast : ((z₀ : ℚ) : ℝ) = (((3 ^ i₀ * q ^ k₀ : ℚ)) : ℝ) := by
      push_cast
      rw [hz₀, hq, ← pow_mul]
    exact_mod_cast hcast
  -- Write `q` over its denominator and identify the denominator as `3 ^ a`.
  set N : ℕ := q.num.toNat with hN
  have hNq : (N : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt (Rat.num_pos.mpr hqpos))
  have hNpos : 0 < N := by
    have := Rat.num_pos.mpr hqpos
    omega
  have hqden : q * (q.den : ℚ) = (N : ℚ) := by
    rw [show ((N : ℚ)) = ((N : ℤ) : ℚ) by push_cast; ring, hNq]
    exact_mod_cast Rat.mul_den_eq_num q
  have hden_dvd : (q.den : ℕ) ∣ 3 ^ i₀ := by
    -- Clear denominators in `z₀ = 3^{i₀} q^{k₀}`.
    have hq_pow : q ^ k₀ * ((q.den : ℚ)) ^ k₀ = (N : ℚ) ^ k₀ := by
      rw [← mul_pow, hqden]
    have hclear : (z₀ : ℚ) * (q.den : ℚ) ^ k₀ = 3 ^ i₀ * (N : ℚ) ^ k₀ := by
      rw [hz₀Q]
      rw [mul_assoc, hq_pow]
    have hclearZ : z₀ * (q.den : ℤ) ^ k₀ = 3 ^ i₀ * (N : ℤ) ^ k₀ := by
      exact_mod_cast hclear
    have hz₀pos : 0 < z₀ := by
      have : (0 : ℝ) < (z₀ : ℝ) := by
        rw [hz₀]
        positivity
      exact_mod_cast this
    have hclearN : z₀.toNat * q.den ^ k₀ = 3 ^ i₀ * N ^ k₀ := by
      have hzt : ((z₀.toNat : ℤ)) = z₀ := Int.toNat_of_nonneg hz₀pos.le
      exact_mod_cast (hzt ▸ hclearZ : (z₀.toNat : ℤ) * (q.den : ℤ) ^ k₀ = _)
    have hdvd1 : q.den ^ k₀ ∣ 3 ^ i₀ * N ^ k₀ := ⟨z₀.toNat, by rw [← hclearN]; ring⟩
    have hcop : Nat.Coprime (q.den ^ k₀) (N ^ k₀) := by
      have hbase : Nat.Coprime q.den N := by
        have := q.reduced
        rw [show q.num.natAbs = N by omega] at this
        exact this.symm
      exact hbase.pow _ _
    have hdvd2 : q.den ^ k₀ ∣ 3 ^ i₀ := hcop.dvd_of_dvd_mul_right hdvd1
    exact dvd_trans (dvd_pow_self q.den hk₀.ne') hdvd2
  obtain ⟨a, ha_le, hden⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hden_dvd
  have hqN : q * (3 ^ a : ℚ) = (N : ℚ) := by
    rw [← hqden, hden]
    push_cast
    ring
  -- The generator and its integral outputs.
  set β : ℝ := (a : ℝ) + α * d with hβ
  set M : ℕ := 2 ^ a * w ^ d with hM
  have h2β : (2 : ℝ) ^ β = M := by
    rw [hβ, Real.rpow_add (by norm_num), Real.rpow_natCast,
      Real.rpow_mul_natCast (by norm_num) α d, h2α, hM]
    push_cast
    ring
  have h3α : (3 : ℝ) ^ α = E := by
    rw [hE, hα, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos hwR, Real.logb, logThreeDivLogTwo]
    congr 1
    ring
  have h3β : (3 : ℝ) ^ β = N := by
    rw [hβ, Real.rpow_add (by norm_num), Real.rpow_natCast,
      Real.rpow_mul_natCast (by norm_num) α d, h3α, hq.symm]
    have := hqN
    have hcast : ((q : ℝ)) * ((3 : ℝ) ^ a) = (N : ℝ) := by
      exact_mod_cast congrArg (fun t : ℚ => (t : ℝ)) hqN
    linarith [hcast]
  have hβpos : 0 < β := by
    rw [hβ]
    have : (0 : ℝ) < α * d := by
      have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
      positivity
    positivity
  have hβirr : Irrational β := by
    rw [hβ]
    have h1 : Irrational (α * d) := hαirr.mul_natCast hd0.ne'
    exact h1.natCast_add a
  -- Forward classification.
  have hforward : ∀ y : ℝ,
      (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
      (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
      ∃ n k : ℕ, y = (n : ℝ) + (k : ℝ) * β := by
    intro y h₂ h₃
    obtain ⟨i, j, hyeq, hmem⟩ := hsol_data y h₂ h₃
    obtain ⟨k, hjk⟩ := hdvd j (by
      obtain ⟨z, hz⟩ := hmem
      have h3i : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
      refine ⟨(z : ℚ) / 3 ^ i, ?_⟩
      push_cast
      rw [hz]
      field_simp)
    obtain ⟨z, hz⟩ := hmem
    have hzQ : (z : ℚ) = 3 ^ i * q ^ k := by
      have hcast : ((z : ℚ) : ℝ) = (((3 ^ i * q ^ k : ℚ)) : ℝ) := by
        push_cast
        rw [hz, hjk, hq, ← pow_mul]
      exact_mod_cast hcast
    -- The two-adic exponent clears the denominator: `a * k ≤ i`.
    have hik : a * k ≤ i := by
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp
      have hq_pow : q ^ k * ((3 : ℚ) ^ a) ^ k = (N : ℚ) ^ k := by
        rw [← mul_pow, hqN]
      have hclear : (z : ℚ) * 3 ^ (a * k) = 3 ^ i * (N : ℚ) ^ k := by
        rw [hzQ, mul_assoc]
        rw [show ((3 : ℚ)) ^ (a * k) = ((3 : ℚ) ^ a) ^ k by rw [← pow_mul]]
        rw [hq_pow]
      have hzpos : 0 < z := by
        have : (0 : ℝ) < (z : ℝ) := by
          rw [hz]
          positivity
        exact_mod_cast this
      have hclearZ : z * (3 : ℤ) ^ (a * k) = 3 ^ i * (N : ℤ) ^ k := by
        exact_mod_cast hclear
      have hzt : ((z.toNat : ℤ)) = z := Int.toNat_of_nonneg hzpos.le
      have hclearN : z.toNat * 3 ^ (a * k) = 3 ^ i * N ^ k := by
        exact_mod_cast (hzt ▸ hclearZ : (z.toNat : ℤ) * (3 : ℤ) ^ (a * k) = _)
      have hdvd1 : 3 ^ (a * k) ∣ 3 ^ i * N ^ k :=
        ⟨z.toNat, by rw [← hclearN]; ring⟩
      have hcop3N : Nat.Coprime 3 N := by
        have hred := q.reduced
        rw [show q.num.natAbs = N by omega, hden] at hred
        have h3d : (3 : ℕ) ∣ 3 ^ a := dvd_pow_self 3 hapos.ne'
        exact ((Nat.coprime_comm.mp (hred.coprime_dvd_right h3d)))
      have hcop : Nat.Coprime (3 ^ (a * k)) (N ^ k) := hcop3N.pow _ _
      have hdvd2 : 3 ^ (a * k) ∣ 3 ^ i := hcop.dvd_of_dvd_mul_right hdvd1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd2
    refine ⟨i - a * k, k, ?_⟩
    have hcast : ((i - a * k : ℕ) : ℝ) = (i : ℝ) - (a : ℝ) * k := by
      push_cast [Nat.cast_sub hik]
      ring
    rw [hyeq, hjk, hcast, hβ]
    push_cast
    ring
  -- Backward: every `n + k β` is a solution.
  have hbackward : ∀ n k : ℕ,
      (2 : ℝ) ^ ((n : ℝ) + (k : ℝ) * β) ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ ((n : ℝ) + (k : ℝ) * β) ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro n k
    constructor
    · refine ⟨((2 ^ n * M ^ k : ℕ) : ℤ), ?_⟩
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast, mul_comm ((k : ℝ)) β,
        Real.rpow_mul_natCast (by norm_num) β k, h2β]
      push_cast
      ring
    · refine ⟨((3 ^ n * N ^ k : ℕ) : ℤ), ?_⟩
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast, mul_comm ((k : ℝ)) β,
        Real.rpow_mul_natCast (by norm_num) β k, h3β]
      push_cast
      ring
  -- Uniqueness of representations.
  have huniq : ∀ n k n' k' : ℕ,
      (n : ℝ) + (k : ℝ) * β = (n' : ℝ) + (k' : ℝ) * β → n = n' ∧ k = k' := by
    intro n k n' k' heq
    have hkk : k = k' := by
      by_contra hne
      have hkR : ((k : ℝ)) - k' ≠ 0 := by
        intro h0
        apply hne
        have : ((k : ℝ)) = k' := by linarith
        exact_mod_cast this
      apply hβirr
      refine ⟨((n' : ℚ) - n) / ((k : ℚ) - k'), ?_⟩
      have hkQ : ((k : ℚ)) - k' ≠ 0 := by
        intro h0
        apply hkR
        have : ((k : ℚ)) = k' := by linarith
        have : ((k : ℝ)) = k' := by exact_mod_cast this
        linarith
      push_cast
      rw [div_eq_iff (by exact_mod_cast hkQ)]
      have hkQR : (((k : ℚ) : ℝ)) - ((k' : ℚ) : ℝ) ≠ 0 := by
        push_cast
        exact hkR
      linarith
    refine ⟨?_, hkk⟩
    subst hkk
    have : ((n : ℝ)) = n' := by linarith
    exact_mod_cast this
  -- Sizes of the outputs.
  have hM1 : 1 < M := by
    rw [hM]
    have hw3 : 3 ≤ w := by
      obtain ⟨s, hs⟩ := hwodd
      omega
    have hwd : w ≤ w ^ d := Nat.le_self_pow hd0.ne' w
    have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    calc 1 < 3 := by norm_num
      _ ≤ w := hw3
      _ ≤ w ^ d := hwd
      _ ≤ 2 ^ a * w ^ d := Nat.le_mul_of_pos_left _ (by positivity)
  have hA1 : 1 < N := by
    have h1 : (1 : ℝ) < (3 : ℝ) ^ β := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
      exact Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr hβpos
    rw [h3β] at h1
    exact_mod_cast h1
  -- Assemble.
  refine ⟨β, M, N, hM1, hA1, h2β, h3β, hβirr, ?_, huniq, ?_⟩
  · intro y
    constructor
    · rintro ⟨h₂, h₃⟩
      exact hforward y h₂ h₃
    · rintro ⟨n, k, rfl⟩
      exact hbackward n k
  · intro y h₂ h₃ hyni
    obtain ⟨n, k, rfl⟩ := hforward y h₂ h₃
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd ⟨(n : ℤ), by push_cast; ring⟩ hyni
    · have hn0 : (0 : ℝ) ≤ n := by positivity
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      nlinarith [hβpos]

end LeanProofs.TwoBaseIntegerExponent
