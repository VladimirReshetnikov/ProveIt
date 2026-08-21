import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator
import ExponentialIdentities.TwoBaseIntegerExponent.Localization

/-!
# The candidate gcd/lcm lattice

The set of two-base natural candidates is closed under `gcd` and `lcm`, unconditionally.

The proof splits on the conjecture but needs no transcendence input on either branch.  If the
conjecture holds the candidates are the powers of two, whose gcds and lcms are again powers of
two.  If it fails, the canonical primitive-generator theorem writes every candidate as
`2 ^ i * w ^ (d * k)` for one fixed odd core `w` and one fixed index `d`, subject to the single
linear inequality `a * k ≤ i`; gcd and lcm act coordinatewise on `(i, k)` by minimum and
maximum, and the inequality is preserved by both.

The arithmetic core is `gcd_two_pow_mul_odd_pow`: for odd `w`, the numbers `2 ^ s * w ^ t` form
a copy of `ℕ²` on which `gcd` and `lcm` are coordinatewise `min` and `max`.  That part is
independent of the conjecture and of this problem.

A byproduct recorded here is prime-support rigidity: under failure, a single odd core `w`
serves every candidate at once, so the whole nonintegral branch is locked onto one finite set
of odd primes.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- With `w` odd, `gcd (2 ^ s₁ * w ^ t₁) (2 ^ s₂ * w ^ t₂) = 2 ^ s₁ * w ^ t₂` whenever the two
exponents are ordered oppositely.  This is the only genuinely mixed case. -/
private theorem gcd_two_pow_mul_odd_pow_of_le {w : ℕ} (hw : Odd w) {s₁ t₁ s₂ t₂ : ℕ}
    (hs : s₁ ≤ s₂) (ht : t₂ ≤ t₁) :
    Nat.gcd (2 ^ s₁ * w ^ t₁) (2 ^ s₂ * w ^ t₂) = 2 ^ s₁ * w ^ t₂ := by
  have h₁ : 2 ^ s₁ * w ^ t₁ = 2 ^ s₁ * w ^ t₂ * w ^ (t₁ - t₂) := by
    have hpow : w ^ t₁ = w ^ t₂ * w ^ (t₁ - t₂) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, mul_assoc]
  have h₂ : 2 ^ s₂ * w ^ t₂ = 2 ^ s₁ * w ^ t₂ * 2 ^ (s₂ - s₁) := by
    have hpow : (2 : ℕ) ^ s₂ = 2 ^ s₁ * 2 ^ (s₂ - s₁) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  have hcop : Nat.Coprime (w ^ (t₁ - t₂)) (2 ^ (s₂ - s₁)) :=
    Nat.Coprime.pow _ _ (Nat.coprime_two_right.mpr hw)
  rw [h₁, h₂, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop, mul_one]

/-- **Coordinatewise gcd.**  For odd `w`, the numbers `2 ^ s * w ^ t` have gcd computed by
taking the minimum in each exponent. -/
theorem gcd_two_pow_mul_odd_pow {w : ℕ} (hw : Odd w) (s₁ t₁ s₂ t₂ : ℕ) :
    Nat.gcd (2 ^ s₁ * w ^ t₁) (2 ^ s₂ * w ^ t₂) = 2 ^ min s₁ s₂ * w ^ min t₁ t₂ := by
  rcases le_total s₁ s₂ with hs | hs <;> rcases le_total t₁ t₂ with ht | ht
  · rw [min_eq_left hs, min_eq_left ht]
    exact Nat.gcd_eq_left (Nat.mul_dvd_mul (pow_dvd_pow 2 hs) (pow_dvd_pow w ht))
  · rw [min_eq_left hs, min_eq_right ht]
    exact gcd_two_pow_mul_odd_pow_of_le hw hs ht
  · rw [min_eq_right hs, min_eq_left ht, Nat.gcd_comm]
    exact gcd_two_pow_mul_odd_pow_of_le hw hs ht
  · rw [min_eq_right hs, min_eq_right ht]
    exact Nat.gcd_eq_right (Nat.mul_dvd_mul (pow_dvd_pow 2 hs) (pow_dvd_pow w ht))

/-- **Coordinatewise lcm.**  The companion of `gcd_two_pow_mul_odd_pow`, obtained from
`gcd * lcm = product` together with `min + max = sum`. -/
theorem lcm_two_pow_mul_odd_pow {w : ℕ} (hw : Odd w) (hwpos : 0 < w) (s₁ t₁ s₂ t₂ : ℕ) :
    Nat.lcm (2 ^ s₁ * w ^ t₁) (2 ^ s₂ * w ^ t₂) = 2 ^ max s₁ s₂ * w ^ max t₁ t₂ := by
  have hprod := Nat.gcd_mul_lcm (2 ^ s₁ * w ^ t₁) (2 ^ s₂ * w ^ t₂)
  rw [gcd_two_pow_mul_odd_pow hw] at hprod
  have hpos : 0 < 2 ^ min s₁ s₂ * w ^ min t₁ t₂ := by positivity
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [hprod]
  have hs : min s₁ s₂ + max s₁ s₂ = s₁ + s₂ := min_add_max s₁ s₂
  have ht : min t₁ t₂ + max t₁ t₂ = t₁ + t₂ := min_add_max t₁ t₂
  calc
    2 ^ s₁ * w ^ t₁ * (2 ^ s₂ * w ^ t₂)
        = 2 ^ (s₁ + s₂) * w ^ (t₁ + t₂) := by ring
    _ = 2 ^ (min s₁ s₂ + max s₁ s₂) * w ^ (min t₁ t₂ + max t₁ t₂) := by rw [hs, ht]
    _ = 2 ^ min s₁ s₂ * w ^ min t₁ t₂ * (2 ^ max s₁ s₂ * w ^ max t₁ t₂) := by ring

/-- Every power of two is a two-base natural candidate. -/
theorem twoBaseNaturalCandidate_two_pow (i : ℕ) : TwoBaseNaturalCandidate (2 ^ i) := by
  refine ⟨Nat.two_pow_pos i, ⟨(3 ^ i : ℤ), ?_⟩⟩
  have hcast : (((2 : ℕ) ^ i : ℕ) : ℝ) = (2 : ℝ) ^ (i : ℕ) := by
    push_cast
    ring
  rw [hcast, ← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), two_rpow_logThreeDivLogTwo, Real.rpow_natCast]
  push_cast
  ring

/-- **Prime-support rigidity.**  If the conjecture fails, a single odd core `w` represents
every candidate at once, so the entire hypothetical branch has one fixed odd prime support. -/
theorem exists_fixed_odd_core_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w : ℕ, Odd w ∧ 1 < w ∧
      ∀ m : ℕ, TwoBaseNaturalCandidate m → ∃ s t : ℕ, m = 2 ^ s * w ^ t := by
  obtain ⟨w, d, a, _c, _β, hwodd, hw1, _h3, _hd, _hc, _ha, _h7, _h8, _hnorm, _h10, _h11,
    _h12, _h13, _h14, _h15, hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  refine ⟨w, hwodd, hw1, ?_⟩
  intro m hm
  obtain ⟨⟨n, k⟩, hnk, _⟩ := (hcand m).mp hm
  refine ⟨n + a * k, d * k, ?_⟩
  rw [hnk, mul_pow, ← pow_mul, ← pow_mul, pow_add]
  ring

/-- **Candidate gcd/lcm lattice, failure branch.**  Conditional on failure, the candidates in
primitive coordinates form a sublattice of `ℕ²`: the constraint `a * k ≤ i` survives
coordinatewise minimum and maximum. -/
theorem twoBaseNaturalCandidate_gcd_lcm_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) {m n : ℕ}
    (hm : TwoBaseNaturalCandidate m) (hn : TwoBaseNaturalCandidate n) :
    TwoBaseNaturalCandidate (Nat.gcd m n) ∧ TwoBaseNaturalCandidate (Nat.lcm m n) := by
  obtain ⟨w, d, a, c, _β, hwodd, hw1, _h3, _hd, hc, ha, _h7, _h8, hnorm, _h10, _h11,
    _h12, _h13, _h14, _h15, hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  have hwpos : 0 < w := by omega
  obtain ⟨⟨n₁, k₁⟩, hnk₁, _⟩ := (hcand m).mp hm
  obtain ⟨⟨n₂, k₂⟩, hnk₂, _⟩ := (hcand n).mp hn
  have hmrep : m = 2 ^ (n₁ + a * k₁) * w ^ (d * k₁) := by
    rw [hnk₁, mul_pow, ← pow_mul, ← pow_mul, pow_add]
    ring
  have hnrep : n = 2 ^ (n₂ + a * k₂) * w ^ (d * k₂) := by
    rw [hnk₂, mul_pow, ← pow_mul, ← pow_mul, pow_add]
    ring
  have hle₁ : a * k₁ ≤ n₁ + a * k₁ := Nat.le_add_left _ _
  have hle₂ : a * k₂ ≤ n₂ + a * k₂ := Nat.le_add_left _ _
  have hcoord : ∀ i k : ℕ, a * k ≤ i → TwoBaseNaturalCandidate (2 ^ i * w ^ (d * k)) :=
    fun i k h => (twoBaseNaturalCandidate_primitive_coordinates_iff (w := w) (d := d)
      (a := a) (c := c) (i := i) (k := k) hwpos hc ha hnorm).mpr h
  constructor
  · rw [hmrep, hnrep, gcd_two_pow_mul_odd_pow hwodd, min_mul_mul_left]
    refine hcoord _ _ (Nat.le_min.mpr ⟨?_, ?_⟩)
    · exact le_trans (Nat.mul_le_mul_left a (min_le_left k₁ k₂)) hle₁
    · exact le_trans (Nat.mul_le_mul_left a (min_le_right k₁ k₂)) hle₂
  · rw [hmrep, hnrep, lcm_two_pow_mul_odd_pow hwodd hwpos, max_mul_mul_left]
    refine hcoord _ _ ?_
    rcases le_total k₁ k₂ with h | h
    · rw [max_eq_right h]
      exact le_trans hle₂ (le_max_right _ _)
    · rw [max_eq_left h]
      exact le_trans hle₁ (le_max_left _ _)

/-- **Candidate gcd lattice.**  Unconditionally, the two-base natural candidates are closed
under `gcd`. -/
theorem twoBaseNaturalCandidate_gcd {m n : ℕ}
    (hm : TwoBaseNaturalCandidate m) (hn : TwoBaseNaturalCandidate n) :
    TwoBaseNaturalCandidate (Nat.gcd m n) := by
  by_cases hconj : AlaogluErdosConjecture
  · obtain ⟨i, hi⟩ := alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp hconj m hm
    obtain ⟨j, hj⟩ := alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp hconj n hn
    subst hi
    subst hj
    have hgcd : Nat.gcd (2 ^ i) (2 ^ j) = 2 ^ min i j := by
      simpa using gcd_two_pow_mul_odd_pow (w := 1) odd_one i 0 j 0
    rw [hgcd]
    exact twoBaseNaturalCandidate_two_pow _
  · exact (twoBaseNaturalCandidate_gcd_lcm_of_not_alaogluErdosConjecture hconj hm hn).1

/-- **Candidate lcm lattice.**  Unconditionally, the two-base natural candidates are closed
under `lcm`. -/
theorem twoBaseNaturalCandidate_lcm {m n : ℕ}
    (hm : TwoBaseNaturalCandidate m) (hn : TwoBaseNaturalCandidate n) :
    TwoBaseNaturalCandidate (Nat.lcm m n) := by
  by_cases hconj : AlaogluErdosConjecture
  · obtain ⟨i, hi⟩ := alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp hconj m hm
    obtain ⟨j, hj⟩ := alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp hconj n hn
    subst hi
    subst hj
    have hlcm : Nat.lcm (2 ^ i) (2 ^ j) = 2 ^ max i j := by
      simpa using lcm_two_pow_mul_odd_pow (w := 1) odd_one one_pos i 0 j 0
    rw [hlcm]
    exact twoBaseNaturalCandidate_two_pow _
  · exact (twoBaseNaturalCandidate_gcd_lcm_of_not_alaogluErdosConjecture hconj hm hn).2

end LeanProofs.TwoBaseIntegerExponent
