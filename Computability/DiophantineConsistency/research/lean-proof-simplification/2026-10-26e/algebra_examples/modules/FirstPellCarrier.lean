import DiophantineConsistency.NativePellBootstrap
import Diophantine.Common.PellInt

/-!
# The first-Pell carrier and its positive witness maps

The Carrier65 transformation replaces the two positive witnesses `h,tau`
by a positive `n`, defining `tau = E*n+k-R`. This module proves both
witness maps using the existing consecutive-product Pell classification.
The rank bounds are explicit hypotheses; no native-window correctness or
consistency statement is assumed or asserted here.
-/

namespace DiophantineConsistency.FirstPellCarrier

open Diophantine Pell

/-- The congruence and the gap after the first positive solution of the
consecutive-product Pell equation. -/
theorem first_norm_facts {E Y tau k : ℕ} (hE : 0 < E) (hY : 0 < Y)
    (hk : 0 < k)
    (hnorm : tau ^ 2 = 1 + (E * Y) * (E * Y + 1) * k ^ 2) :
    (E : ℤ) ∣ (tau : ℤ) - 1 ∧ k < tau ∧
      (k = 2 ∨ 4 * (2 * (E * Y) + 1) ≤ k) := by
  have hQ : 0 < E * Y := Nat.mul_pos hE hY
  have hP : 1 < 2 * (E * Y) + 1 := by omega
  obtain ⟨r, hr, ht, hk'⟩ :=
    NativePellBootstrap.first_norm_classification hQ hk hnorm
  have htrace : (E : ℤ) ∣ (tau : ℤ) - 1 := by
    rw [ht, xn_eq_xr hP]
    have hbase : ((2 * (E * Y) + 1 : ℕ) : ℤ) ≡ 1 [ZMOD (E : ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-2 * (Y : ℤ), ?_⟩
      push_cast
      ring
    exact Int.modEq_iff_dvd.mp (by simpa only [xr_one] using (xr_modEq hbase r).symm)
  have hkt : k < tau := by
    have hc : 1 ≤ (E * Y) * (E * Y + 1) :=
      Nat.succ_le_of_lt (Nat.mul_pos hQ (by omega))
    have hs : k ^ 2 ≤ (E * Y) * (E * Y + 1) * k ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (k ^ 2) hc
    have hsq : k ^ 2 < tau ^ 2 := by omega
    exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  refine ⟨htrace, hkt, ?_⟩
  by_cases hr1 : r = 1
  · left
    simpa only [hr1, yn_one, mul_one] using hk'
  · right
    have hr2 : 2 ≤ r := by omega
    have hmono := (strictMono_y hP).monotone hr2
    have hy2 : yn hP 2 = 2 * (2 * (E * Y) + 1) := ψ_two hP
    rw [hy2] at hmono
    rw [hk']
    omega

/-- Integer inputs may use the classification after positivity of the
carrier has been established. The congruence is over the integers. -/
theorem first_norm_facts_int {E Y tau k : ℤ} (hE : 0 < E) (hY : 0 < Y)
    (ht : 0 < tau) (hk : 0 < k)
    (hnorm : tau ^ 2 - (E * Y) * (E * Y + 1) * k ^ 2 = 1) :
    E ∣ tau - 1 ∧ k < tau ∧ (k = 2 ∨ 4 * (2 * (E * Y) + 1) ≤ k) := by
  lift E to ℕ using hE.le
  lift Y to ℕ using hY.le
  lift tau to ℕ using ht.le
  lift k to ℕ using hk.le
  have hE' : 0 < E := by exact_mod_cast hE
  have hY' : 0 < Y := by exact_mod_cast hY
  have hk' : 0 < k := by exact_mod_cast hk
  have hn : tau ^ 2 = 1 + (E * Y) * (E * Y + 1) * k ^ 2 := by
    have he : (tau : ℤ) ^ 2 = 1 + (E * Y) * (E * Y + 1) * k ^ 2 := by
      linarith only [hnorm]
    exact_mod_cast he
  obtain ⟨htrace, hkt, hgap⟩ := first_norm_facts hE' hY' hk' hn
  exact ⟨htrace, by exact_mod_cast hkt, by exact_mod_cast hgap⟩

/-- Every positive new carrier satisfying the first norm restores a
strictly positive omitted quotient `h`; its trace is also positive.
No sign hypothesis on the abbreviation `tau` is needed. -/
theorem restore_quotient {E Y k n R tau : ℤ}
    (hE : 0 < E) (hY : 0 < Y) (hk : 0 < k) (hn : 0 < n)
    (hR : 1 < R) (hcap : R + 2 < E)
    (hcarrier : tau = E * n + k - R)
    (hnorm : tau ^ 2 - (E * Y) * (E * Y + 1) * k ^ 2 = 1) :
    0 < tau ∧ ∃ h : ℤ, 0 < h ∧ k - h * E - R = 1 := by
  have hn1 : 1 ≤ n := hn
  have hEn : E ≤ E * n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn1 hE.le
  have ht : 0 < tau := by omega
  obtain ⟨htrace, _, hgap⟩ := first_norm_facts_int hE hY ht hk hnorm
  have hdiv : E ∣ k - R - 1 := by
    have he : tau - 1 - E * n = k - R - 1 := by rw [hcarrier]; ring
    rw [← he]
    exact dvd_sub htrace (dvd_mul_right E n)
  obtain ⟨h, hh⟩ := hdiv
  have hquot : k - h * E - R = 1 := by nlinarith only [hh]
  have hh0 : 0 ≤ h := by
    by_contra hneg
    have hh1 : h ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hh1 hE.le
    nlinarith only [hh, hmul, hk, hcap]
  have hhpos : 0 < h := by
    by_contra hnot
    have hz : h = 0 := by omega
    have hkR : k = R + 1 := by rw [hz] at hquot; linarith only [hquot]
    rcases hgap with htwo | hlarge
    · omega
    · have hY1 : 1 ≤ Y := hY
      have hEY : E ≤ E * Y := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hY1 hE.le
      omega
  exact ⟨ht, h, hhpos, hquot⟩

/-- A positive parent first norm and its index equation supply a positive
new carrier. The old first root is recovered exactly. -/
theorem restore_carrier {E Y k h R tau : ℤ}
    (hE : 0 < E) (hY : 0 < Y) (hk : 0 < k) (ht : 0 < tau)
    (hR : 0 < R)
    (hindex : k - h * E - R = 1)
    (hnorm : tau ^ 2 - (E * Y) * (E * Y + 1) * k ^ 2 = 1) :
    ∃ n : ℤ, 0 < n ∧ tau = E * n + k - R := by
  obtain ⟨htrace, hkt, _⟩ := first_norm_facts_int hE hY ht hk hnorm
  have hdiv : E ∣ tau - k + R := by
    have he : tau - k + R = (tau - 1) - E * h := by nlinarith only [hindex]
    rw [he]
    exact dvd_sub htrace (dvd_mul_right E h)
  obtain ⟨n, hn⟩ := hdiv
  have hnpos : 0 < n := by
    have hproduct : 0 < E * n := by rw [← hn]; omega
    exact (mul_pos_iff_of_pos_left hE).mp hproduct
  exact ⟨n, hnpos, by nlinarith only [hn]⟩

/-- The restored quotient is unique, so restoring an existing parent
quotient returns that same integer. -/
theorem quotient_unique {E k R h₁ h₂ : ℤ} (hE : E ≠ 0)
    (h₁eq : k - h₁ * E - R = 1) (h₂eq : k - h₂ * E - R = 1) : h₁ = h₂ := by
  apply mul_right_cancel₀ hE
  linarith only [h₁eq, h₂eq]

/-- The carrier is unique, so the two witness maps are inverse whenever
the positive parent interface is available. -/
theorem carrier_unique {E k R tau n₁ n₂ : ℤ} (hE : E ≠ 0)
    (h₁eq : tau = E * n₁ + k - R) (h₂eq : tau = E * n₂ + k - R) : n₁ = n₂ := by
  apply mul_left_cancel₀ hE
  linarith only [h₁eq, h₂eq]

/-- Under the stated rank window, the new positive carrier and the old
positive trace/index interface have exactly the same existence predicate. -/
theorem exists_carrier_iff_index {E Y k R tau : ℤ}
    (hE : 0 < E) (hY : 0 < Y) (hk : 0 < k)
    (hR : 1 < R) (hcap : R + 2 < E)
    (hnorm : tau ^ 2 - (E * Y) * (E * Y + 1) * k ^ 2 = 1) :
    (∃ n : ℤ, 0 < n ∧ tau = E * n + k - R) ↔
      (0 < tau ∧ ∃ h : ℤ, 0 < h ∧ k - h * E - R = 1) := by
  constructor
  · rintro ⟨n, hn, hcarrier⟩
    exact restore_quotient hE hY hk hn hR hcap hcarrier hnorm
  · rintro ⟨ht, h, _, hindex⟩
    exact restore_carrier hE hY hk ht (by omega) hindex hnorm

end DiophantineConsistency.FirstPellCarrier
