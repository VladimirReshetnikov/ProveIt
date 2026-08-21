import ExponentialIdentities.TwoBaseIntegerExponent.OddCore

/-!
# The canonical primitive odd core

This file normalizes the common odd core by the gcd of its positive prime valuations.
Conditional on the existence of a non-dyadic candidate, it proves that this normalized core is
unique and that every candidate has unique coordinates `2 ^ i * w ^ j`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Finset

noncomputable section

/-- A natural base is primitive when it is not a proper power of a smaller base. -/
def NatPowerPrimitive (w : ℕ) : Prop :=
  ∀ c k : ℕ, 1 < c → 2 ≤ k → w ≠ c ^ k

/-- An odd core represents all natural candidates. -/
def CommonOddCore (w : ℕ) : Prop :=
  Odd w ∧ 1 < w ∧
    ∀ m : ℕ, TwoBaseNaturalCandidate m → ∃ i j : ℕ, m = 2 ^ i * w ^ j

/-- The gcd of the positive prime valuations of `w`. When `w` is odd, these are exactly
the positive odd-prime valuations appearing in the canonical normalization. -/
def oddPrimeValuationGCD (w : ℕ) : ℕ :=
  w.primeFactors.gcd w.factorization

private theorem exists_pow_eq_of_dvd_factorization {w d : ℕ}
    (hw0 : w ≠ 0) (hdiv : ∀ p : ℕ, d ∣ w.factorization p) :
    ∃ c : ℕ, w = c ^ d := by
  let factors := w.factorization.mapRange (fun e : ℕ ↦ e / d) (Nat.zero_div d)
  set c := factors.prod (· ^ ·) with hc
  refine ⟨c, ?_⟩
  apply Nat.eq_of_factorization_eq hw0 (by simp [c, factors])
  intro p
  have hprime (q : ℕ) (hq : q ∈ factors.support) : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hq)
  rw [Nat.factorization_pow, hc, Nat.prod_pow_factorization_eq_self hprime]
  simp [factors, Nat.mul_div_cancel' (hdiv p)]

/-- Gcd-normalization implies the equivalent power-theoretic primitivity condition. -/
theorem natPowerPrimitive_of_oddPrimeValuationGCD_eq_one {w : ℕ}
    (hgcd : oddPrimeValuationGCD w = 1) : NatPowerPrimitive w := by
  intro c k hc hk hwck
  have hkdvd : k ∣ oddPrimeValuationGCD w := by
    apply Finset.dvd_gcd
    intro p hp
    rw [hwck, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    exact ⟨c.factorization p, rfl⟩
  rw [hgcd] at hkdvd
  have hk1 : k ≤ 1 := Nat.le_of_dvd (by norm_num) hkdvd
  omega

/-- For a number greater than one, absence of proper-power structure forces gcd-normalized
prime valuations. -/
theorem oddPrimeValuationGCD_eq_one_of_natPowerPrimitive {w : ℕ}
    (hw1 : 1 < w) (hprimitive : NatPowerPrimitive w) :
    oddPrimeValuationGCD w = 1 := by
  let d := oddPrimeValuationGCD w
  have hw0 : w ≠ 0 := ne_of_gt (Nat.zero_lt_one.trans hw1)
  have hpprime : w.minFac.Prime := Nat.minFac_prime (by omega)
  have hpdvd : w.minFac ∣ w := Nat.minFac_dvd w
  have hpmem : w.minFac ∈ w.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hpprime, hpdvd, hw0⟩
  have hpval : w.factorization w.minFac ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (by simpa using hpmem)
  have hd0 : d ≠ 0 := by
    intro hd
    apply hpval
    apply (Finset.gcd_eq_zero_iff.mp ?_) w.minFac hpmem
    exact hd
  have hdiv : ∀ p : ℕ, d ∣ w.factorization p := by
    intro p
    by_cases hp : p ∈ w.primeFactors
    · exact Finset.gcd_dvd hp
    · have hz : w.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa using hp)
      simp [hz]
  by_contra hd1
  have hd2 : 2 ≤ d :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hd0, hd1⟩
  obtain ⟨c, hwc⟩ := exists_pow_eq_of_dvd_factorization hw0 hdiv
  have hc1 : 1 < c := by
    apply (one_lt_pow_iff hd0).mp
    rw [← hwc]
    exact hw1
  exact hprimitive c d hc1 hd2 hwc

private theorem two_pow_mul_odd_pow_injective {w : ℕ}
    (hwodd : Odd w) (hw1 : 1 < w) :
    Function.Injective (fun ij : ℕ × ℕ ↦ 2 ^ ij.1 * w ^ ij.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hw0 : w ≠ 0 := by omega
  have hwfac : w.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hwodd.not_two_dvd_nat
  have hfac := congrArg (fun n : ℕ ↦ n.factorization 2) h
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (pow_ne_zero _ hw0),
    Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (pow_ne_zero _ hw0),
    Nat.factorization_pow, Nat.factorization_pow,
    Nat.factorization_pow, Nat.factorization_pow] at hfac
  have hi : i = i' := by
    simpa [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
      (by norm_num : Nat.Prime 2).factorization_self, hwfac] using hfac
  subst i'
  have hjpow : w ^ j = w ^ j' :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < (2 : ℕ)) i) h
  have hj : j = j' := Nat.pow_right_injective (by omega) hjpow
  exact Prod.ext rfl hj

/-- There is always a least common odd core, and it cannot itself be a proper power. -/
theorem exists_primitive_common_odd_core :
    ∃ w : ℕ, CommonOddCore w ∧ NatPowerPrimitive w := by
  classical
  have hex : ∃ w : ℕ, CommonOddCore w := exists_common_odd_core
  let w := Nat.find hex
  have hw : CommonOddCore w := Nat.find_spec hex
  have hwmin : ∀ t : ℕ, t < w → ¬ CommonOddCore t := fun t ht ↦ Nat.find_min hex ht
  refine ⟨w, hw, ?_⟩
  intro c k hc hk hwck
  have hcw : c < w := by
    have hlt := Nat.pow_lt_pow_right hc (show 1 < k by omega)
    rw [pow_one, ← hwck] at hlt
    exact hlt
  apply hwmin c hcw
  have hcodd : Odd c := by
    apply Odd.of_dvd_nat hw.1
    rw [hwck]
    exact dvd_pow_self c (by omega)
  refine ⟨hcodd, hc, ?_⟩
  intro m hm
  obtain ⟨i, j, hij⟩ := hw.2.2 m hm
  exact ⟨i, k * j, by simpa [hwck, pow_mul] using hij⟩

private theorem primitive_common_odd_core_unique
    (hcounter : ∃ a : ℕ,
      TwoBaseNaturalCandidate a ∧ ¬ ∃ n : ℕ, a = 2 ^ n)
    {w v : ℕ}
    (hw : CommonOddCore w) (hwp : NatPowerPrimitive w)
    (hv : CommonOddCore v) (hvp : NatPowerPrimitive v) :
    w = v := by
  obtain ⟨a, ha, hanot⟩ := hcounter
  obtain ⟨i, j, haij⟩ := hw.2.2 a ha
  obtain ⟨i', j', haij'⟩ := hv.2.2 a ha
  have hj0 : j ≠ 0 := by
    intro hj
    apply hanot
    exact ⟨i, by simpa [hj] using haij⟩
  have hj0' : j' ≠ 0 := by
    intro hj
    apply hanot
    exact ⟨i', by simpa [hj] using haij'⟩
  have hw0 : w ≠ 0 := ne_of_gt (Nat.zero_lt_one.trans hw.2.1)
  have hv0 : v ≠ 0 := ne_of_gt (Nat.zero_lt_one.trans hv.2.1)
  have hwfac : w.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hw.1.not_two_dvd_nat
  have hvfac : v.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hv.1.not_two_dvd_nat
  have hprod : 2 ^ i * w ^ j = 2 ^ i' * v ^ j' := haij.symm.trans haij'
  have hfac := congrArg (fun n : ℕ ↦ n.factorization 2) hprod
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (pow_ne_zero _ hw0),
    Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (pow_ne_zero _ hv0),
    Nat.factorization_pow, Nat.factorization_pow,
    Nat.factorization_pow, Nat.factorization_pow] at hfac
  have hii : i = i' := by
    simpa [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
      (by norm_num : Nat.Prime 2).factorization_self, hwfac, hvfac] using hfac
  subst i'
  have hpows : w ^ j = v ^ j' :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < (2 : ℕ)) i) hprod
  obtain ⟨c, hwc, hvc⟩ :=
    Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hj0) hpows
  let g := Nat.gcd j j'
  change w = c ^ (j' / g) at hwc
  change v = c ^ (j / g) at hvc
  have hew0 : j' / g ≠ 0 := by
    intro he
    rw [he, pow_zero] at hwc
    exact (ne_of_gt hw.2.1) hwc
  have hev0 : j / g ≠ 0 := by
    intro he
    rw [he, pow_zero] at hvc
    exact (ne_of_gt hv.2.1) hvc
  have hc1 : 1 < c := by
    apply (one_lt_pow_iff hew0).mp
    rw [← hwc]
    exact hw.2.1
  have hew : j' / g = 1 := by
    by_contra hne
    have hew2 : 2 ≤ j' / g :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hew0, hne⟩
    exact hwp c (j' / g) hc1 hew2 hwc
  have hev : j / g = 1 := by
    by_contra hne
    have hev2 : 2 ≤ j / g :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hev0, hne⟩
    exact hvp c (j / g) hc1 hev2 hvc
  rw [hew, pow_one] at hwc
  rw [hev, pow_one] at hvc
  exact hwc.trans hvc.symm

/-- Conditional on a non-dyadic candidate, the primitive common odd core is canonical;
for that core, the two exponent coordinates of every candidate are unique. -/
theorem existsUnique_primitive_common_odd_core
    (hcounter : ∃ a : ℕ,
      TwoBaseNaturalCandidate a ∧ ¬ ∃ n : ℕ, a = 2 ^ n) :
    ∃! w : ℕ,
      Odd w ∧ 1 < w ∧ oddPrimeValuationGCD w = 1 ∧
        ∀ m : ℕ, TwoBaseNaturalCandidate m →
          ∃! ij : ℕ × ℕ, m = 2 ^ ij.1 * w ^ ij.2 := by
  obtain ⟨w, hw, hwp⟩ := exists_primitive_common_odd_core
  have hinj := two_pow_mul_odd_pow_injective hw.1 hw.2.1
  have hwgcd := oddPrimeValuationGCD_eq_one_of_natPowerPrimitive hw.2.1 hwp
  refine ⟨w, ⟨hw.1, hw.2.1, hwgcd, ?_⟩, ?_⟩
  · intro m hm
    obtain ⟨i, j, hij⟩ := hw.2.2 m hm
    refine ⟨(i, j), hij, ?_⟩
    intro ij hij'
    exact hinj (hij'.symm.trans hij)
  · intro v hv
    symm
    apply primitive_common_odd_core_unique hcounter hw hwp
    · exact ⟨hv.1, hv.2.1, fun m hm ↦ by
        obtain ⟨ij, hij, _⟩ := hv.2.2.2 m hm
        exact ⟨ij.1, ij.2, hij⟩⟩
    · exact natPowerPrimitive_of_oddPrimeValuationGCD_eq_one hv.2.2.1

end

end LeanProofs.TwoBaseIntegerExponent
