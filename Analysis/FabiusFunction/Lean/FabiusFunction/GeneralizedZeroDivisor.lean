import FabiusFunction.GeneralizedRvachevEntire

/-!
# The complete zero divisor of `Φ_a`

`GeneralizedRvachevProduct` characterises the zero set of the
generalized Rvachev transform in *scale* coordinates,

`Φ_a(z) = 0 ↔ ∃ h, a h ≠ 0 ∧ ∃ k ≠ 0, z = k · 2^h`,

and its header says of that description: "the identification of the
two descriptions is not carried out here, and the multiplicity of
each zero is not computed here either."  Both are done here.

In arithmetic coordinates the zero set is exactly the set of nonzero
integers whose multiplicity does not vanish,

`Φ_a(z) = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n ∧ m_a(|n|) ≠ 0`,

and with `GeneralizedRvachevEntire` supplying the order at `±n`, the
two together give the full divisor of an entire function: `Φ_a`
vanishes precisely on `{n ∈ ℤ : n ≠ 0, m_a(|n|) > 0}`, to order
exactly `m_a(|n|)` at each such point, and nowhere else in `ℂ`.

The bridge between the two coordinate systems is arithmetic, not
analytic: `m_a(m) = ∑_{h ≤ v₂(m)} a_h` is a sum of naturals, so it is
nonzero exactly when some `a_h` with `h ≤ v₂(m)` is, and `h ≤ v₂(m)`
is `2^h ∣ m`.  That is `weightedScaleMultiplicity_two_ne_zero_iff`,
which needs `m ≠ 0`: at `m = 0` the convention `v₂(0) = 0` leaves the
left side `a 0`, while every `2^h` divides `0`.

* `Fabius.weightedScaleMultiplicity_two_ne_zero_iff` — the arithmetic
  bridge;
* `Fabius.generalizedRvachevProduct_eq_zero_iff_int` — **the zero set
  in arithmetic coordinates**;
* `Fabius.generalizedRvachevProduct_ne_zero_of_not_int` — in
  particular `Φ_a` has no zeros off the integers, hence none off the
  real axis;
* `Fabius.analyticOrderAt_generalizedRvachevProduct_int` — **the
  order at every nonzero integer**, both signs at once;
* `Fabius.analyticOrderAt_generalizedRvachevProduct_int_ne_zero_iff` —
  the two combined: the order is nonzero exactly on the zero set.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The arithmetic bridge -/

/-- `m_a(m) ≠ 0` exactly when some layer dividing `m` carries a
nonzero weight.  The multiplicity is a sum of naturals over
`h ≤ v₂(m)`, and `h ≤ v₂(m)` is `2^h ∣ m`.

`m ≠ 0` is needed: at `m = 0` the convention `v₂(0) = 0` leaves the
left side `a 0`, while every `2^h` divides `0`. -/
theorem weightedScaleMultiplicity_two_ne_zero_iff (a : ℕ → ℕ) {m : ℕ}
    (hm : m ≠ 0) :
    weightedScaleMultiplicity 2 a m ≠ 0
      ↔ ∃ h : ℕ, 2 ^ h ∣ m ∧ a h ≠ 0 := by
  have hdvd : ∀ h : ℕ, (2 : ℕ) ^ h ∣ m ↔ h ≤ padicValNat 2 m := fun h =>
    padicValNat_dvd_iff_le_of_ne_one (by norm_num) hm
  rw [weightedScaleMultiplicity, inclusivePrefixSum, Ne,
    Finset.sum_eq_zero_iff]
  push_neg
  constructor
  · rintro ⟨h, hmem, hah⟩
    exact ⟨h, (hdvd h).mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)),
      hah⟩
  · rintro ⟨h, hdv, hah⟩
    exact ⟨h, Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr ((hdvd h).mp hdv)), hah⟩

/-! ## The zero set in arithmetic coordinates -/

/-- **The zero set of `Φ_a`.**  In place of the scale description
`∃ h, a h ≠ 0 ∧ ∃ k ≠ 0, z = k · 2^h`, the arithmetic one:

`Φ_a(z) = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n ∧ m_a(|n|) ≠ 0`.

The two agree because `k · 2^h` with `k ≠ 0` ranges over exactly the
nonzero integers divisible by `2^h`, and divisibility by `2^h` is
`h ≤ v₂`. -/
theorem generalizedRvachevProduct_eq_zero_iff_int (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) :
    generalizedRvachevProduct a z = 0 ↔
      ∃ n : ℤ, n ≠ 0 ∧ z = (n : ℂ) ∧
        weightedScaleMultiplicity 2 a n.natAbs ≠ 0 := by
  rw [generalizedRvachevProduct_eq_zero_iff a ha z]
  constructor
  · rintro ⟨h, hah, k, hk0, hzk⟩
    have h2 : (2 : ℤ) ^ h ≠ 0 := pow_ne_zero h two_ne_zero
    refine ⟨k * 2 ^ h, mul_ne_zero hk0 h2, ?_, ?_⟩
    · rw [hzk]
      push_cast
      ring
    · have hnat : (k * 2 ^ h).natAbs = k.natAbs * 2 ^ h := by
        rw [Int.natAbs_mul, Int.natAbs_pow]
        norm_num
      have hne : (k * 2 ^ h).natAbs ≠ 0 :=
        Int.natAbs_ne_zero.mpr (mul_ne_zero hk0 h2)
      refine (weightedScaleMultiplicity_two_ne_zero_iff a hne).mpr
        ⟨h, ?_, hah⟩
      rw [hnat]
      exact Dvd.intro_left _ rfl
  · rintro ⟨n, hn0, hzn, hmult⟩
    have hne : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn0
    obtain ⟨h, hdvd, hah⟩ :=
      (weightedScaleMultiplicity_two_ne_zero_iff a hne).mp hmult
    have hdvdZ : (2 : ℤ) ^ h ∣ n := by
      have hcast : ((2 ^ h : ℕ) : ℤ) ∣ ((n.natAbs : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hdvd
      rw [Int.dvd_natAbs] at hcast
      simpa using hcast
    obtain ⟨k, hk⟩ := hdvdZ
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hn0 (by simpa using hk)
    refine ⟨h, hah, k, hk0, ?_⟩
    rw [hzn, hk]
    push_cast
    ring

/-- `Φ_a` has no zeros off the integers.  In particular it has none
off the real axis, and none at a non-integer real point. -/
theorem generalizedRvachevProduct_ne_zero_of_not_int (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {z : ℂ}
    (hz : ∀ n : ℤ, z ≠ (n : ℂ)) :
    generalizedRvachevProduct a z ≠ 0 := by
  intro hzero
  obtain ⟨n, _, hzn, _⟩ :=
    (generalizedRvachevProduct_eq_zero_iff_int a ha z).mp hzero
  exact hz n hzn

/-! ## The order at every nonzero integer -/

/-- **The order of vanishing at an arbitrary nonzero integer**, both
signs at once:

`analyticOrderAt Φ_a n = m_a(|n|)`,  `n ∈ ℤ`, `n ≠ 0`.

This merges the two halves of `GeneralizedRvachevEntire`.  Together
with `generalizedRvachevProduct_eq_zero_iff_int` it is the complete
divisor of `Φ_a`: the function is entire, vanishes exactly at the
nonzero integers of positive multiplicity, and to exactly that
order. -/
theorem analyticOrderAt_generalizedRvachevProduct_int (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {n : ℤ}
    (hn : n ≠ 0) :
    analyticOrderAt (generalizedRvachevProduct a) ((n : ℤ) : ℂ)
      = ((weightedScaleMultiplicity 2 a n.natAbs : ℕ) : ℕ∞) := by
  have hpos : 1 ≤ n.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
  rcases Int.natAbs_eq n with heq | heq
  · have hc : ((n : ℤ) : ℂ) = ((n.natAbs : ℕ) : ℂ) := by
      conv_lhs => rw [heq]
      exact Int.cast_natCast _
    rw [hc]
    exact analyticOrderAt_generalizedRvachevProduct_pos a ha hpos
  · have hc : ((n : ℤ) : ℂ) = -((n.natAbs : ℕ) : ℂ) := by
      conv_lhs => rw [heq]
      rw [Int.cast_neg, Int.cast_natCast]
    rw [hc]
    exact analyticOrderAt_generalizedRvachevProduct_neg_pos a ha hpos

/-- The order is nonzero exactly on the zero set: at a nonzero
integer, `Φ_a` vanishes iff its multiplicity does not. -/
theorem analyticOrderAt_generalizedRvachevProduct_int_ne_zero_iff
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {n : ℤ}
    (hn : n ≠ 0) :
    analyticOrderAt (generalizedRvachevProduct a) ((n : ℤ) : ℂ) ≠ 0
      ↔ generalizedRvachevProduct a ((n : ℤ) : ℂ) = 0 := by
  rw [analyticOrderAt_generalizedRvachevProduct_int a ha hn,
    generalizedRvachevProduct_eq_zero_iff_int a ha]
  constructor
  · intro hord
    exact ⟨n, hn, rfl, by simpa using hord⟩
  · rintro ⟨m, hm0, hmz, hmult⟩
    have hmn : m = n := by exact_mod_cast hmz.symm
    subst hmn
    simpa using hmult

end Fabius
