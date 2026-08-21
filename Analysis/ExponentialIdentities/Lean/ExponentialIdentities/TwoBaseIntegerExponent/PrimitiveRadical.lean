import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveOddCore
import ExponentialIdentities.TwoBaseIntegerExponent.RadicalReformulation

/-!
# Reduction to primitive localized radicals

The localized-radical reformulation initially quantifies over every odd `u > 1`.  Every such
integer is uniquely a positive power of a base which is not itself a proper power.  This file
formalizes that normalization and proves that the Alaoglu--Erdős conjecture is equivalent to
excluding localized radicals only for these canonical primitive bases.
-/

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-- Every natural number greater than one has a representation as a positive power of a
power-primitive base. -/
theorem exists_primitivePowerDecomposition {u : ℕ} (hu : 1 < u) :
    ∃ w d : ℕ, 1 < w ∧ 0 < d ∧ NatPowerPrimitive w ∧ u = w ^ d := by
  classical
  have hex : ∃ w : ℕ, ∃ d : ℕ, 0 < d ∧ u = w ^ d :=
    ⟨u, 1, by norm_num, by simp⟩
  let w := Nat.find hex
  obtain ⟨d, hd, hud⟩ := Nat.find_spec hex
  change u = w ^ d at hud
  have hwmin : ∀ c : ℕ, c < w → ¬ ∃ e : ℕ, 0 < e ∧ u = c ^ e := by
    intro c hc
    exact Nat.find_min hex hc
  have hwone : 1 < w := by
    have hw0 : w ≠ 0 := by
      intro hw
      rw [hw, zero_pow hd.ne'] at hud
      omega
    have hw1 : w ≠ 1 := by
      intro hw
      rw [hw, one_pow] at hud
      omega
    omega
  have hwprimitive : NatPowerPrimitive w := by
    intro c k hc hk hwck
    have hcw : c < w := by
      have hlt := Nat.pow_lt_pow_right hc (show 1 < k by omega)
      rw [pow_one, ← hwck] at hlt
      exact hlt
    apply hwmin c hcw
    refine ⟨k * d, Nat.mul_pos (by omega) hd, ?_⟩
    rw [hud, hwck, pow_mul]
  exact ⟨w, d, hwone, hd, hwprimitive, hud⟩

/-- The primitive-power decomposition of a number greater than one is unique.  Both the
primitive base and its positive exponent are canonical. -/
theorem existsUnique_primitivePowerDecomposition {u : ℕ} (hu : 1 < u) :
    ∃! wd : ℕ × ℕ,
      1 < wd.1 ∧ 0 < wd.2 ∧ NatPowerPrimitive wd.1 ∧ u = wd.1 ^ wd.2 := by
  obtain ⟨w, d, hw, hd, hwp, hud⟩ := exists_primitivePowerDecomposition hu
  refine ⟨(w, d), ⟨hw, hd, hwp, hud⟩, ?_⟩
  rintro ⟨v, e⟩ ⟨hv, he, hvp, hue⟩
  have hpows : w ^ d = v ^ e := hud.symm.trans hue
  obtain ⟨c, hwc, hvc⟩ :=
    Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hd.ne') hpows
  let g := Nat.gcd d e
  change w = c ^ (e / g) at hwc
  change v = c ^ (d / g) at hvc
  have hediv0 : e / g ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hwc
    omega
  have hddiv0 : d / g ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hvc
    omega
  have hc : 1 < c := by
    apply (one_lt_pow_iff hediv0).mp
    rw [← hwc]
    exact hw
  have hediv : e / g = 1 := by
    by_contra hne
    exact hwp c (e / g) hc
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hediv0, hne⟩) hwc
  have hddiv : d / g = 1 := by
    by_contra hne
    exact hvp c (d / g) hc
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hddiv0, hne⟩) hvc
  have hwv : w = v := by
    rw [hediv, pow_one] at hwc
    rw [hddiv, pow_one] at hvc
    exact hwc.trans hvc.symm
  have hpoww : w ^ d = w ^ e := by simpa [← hwv] using hpows
  have hde : d = e := Nat.pow_right_injective (by omega) hpoww
  exact Prod.ext hwv.symm hde.symm

/-- Oddness passes from a positive power to its primitive base. -/
theorem odd_of_eq_primitivePower {u w d : ℕ}
    (huodd : Odd u) (hd : 0 < d) (huw : u = w ^ d) : Odd w := by
  apply Odd.of_dvd_nat huodd
  rw [huw]
  exact dvd_pow_self w hd.ne'

/-- The normalized remaining obstruction: no positive power of a power-primitive odd base
may acquire an integral `log 3 / log 2` power after clearing a power of three. -/
def PrimitiveOddLocalizedRadicalExclusion : Prop :=
  ∀ w d a B : ℕ,
    Odd w → 1 < w → NatPowerPrimitive w → 0 < d →
      (3 : ℝ) ^ a * ((w : ℝ) ^ logThreeDivLogTwo) ^ d ≠ (B : ℝ)

/-- Quantifying over primitive odd bases and positive powers is exactly equivalent to the
original localized-radical exclusion. -/
theorem oddLocalizedRadicalExclusion_iff_primitive :
    OddLocalizedRadicalExclusion ↔ PrimitiveOddLocalizedRadicalExclusion := by
  constructor
  · intro h w d a B hwodd hw hwp hd heq
    apply h (w ^ d) a B hwodd.pow (one_lt_pow₀ hw hd.ne')
    rw [Nat.cast_pow]
    rw [← Real.rpow_pow_comm (by positivity)]
    exact heq
  · intro h u a B huodd hu heq
    obtain ⟨w, d, hw, hd, hwp, huw⟩ := exists_primitivePowerDecomposition hu
    have hwodd : Odd w := odd_of_eq_primitivePower huodd hd huw
    apply h w d a B hwodd hw hwp hd
    rw [Real.rpow_pow_comm (by positivity)]
    rw [← Nat.cast_pow, ← huw]
    exact heq

/-- The Alaoglu--Erdős conjecture is equivalent to the canonical primitive localized-radical
exclusion.  This removes all redundant proper-power bases from the transcendence target. -/
theorem alaogluErdosConjecture_iff_primitiveOddLocalizedRadicalExclusion :
    AlaogluErdosConjecture ↔ PrimitiveOddLocalizedRadicalExclusion := by
  rw [alaogluErdosConjecture_iff_oddLocalizedRadicalExclusion,
    oddLocalizedRadicalExclusion_iff_primitive]

end

end LeanProofs.TwoBaseIntegerExponent
