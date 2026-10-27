import DiophantineConsistency.NativeAdaptiveMersenne

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveMersenneChecks
open NativeAdaptiveMersenne

example : ¬(15:ℤ)∣3*(2:ℤ)^0-1 := mersenne_not_dvd_three_power (d := 4) (by omega)
example : ¬(15:ℤ)∣3*(2:ℤ)^3-1 := mersenne_not_dvd_three_power (d := 4) (by omega)
example : ¬(15:ℤ)∣3*(2:ℤ)^7-1 := mersenne_not_dvd_three_power (d := 4) (by omega)

-- q=1 is the actual boundary excluded by the positive-exponent premise.
example : (15:ℤ)∣(1:ℤ)-1 ∧ (1:ℤ)∣3*(2:ℤ)^0 := by norm_num
example {R : ℕ} (h : (2:ℤ)^R=1) : ¬∃q : ℤ, 1<q ∧ (15:ℤ)∣q-1 ∧ q∣3*(2:ℤ)^R := by
  rintro ⟨q,hq,hres,hdiv⟩
  obtain ⟨_,hpow,_⟩ := mersenne_base_recovery (d := 4) (by omega) hq hres hdiv
  rw [h] at hpow
  have hh := Int.le_of_dvd (by norm_num : (0:ℤ)<1) hpow
  omega

example {R : ℕ} {q : ℤ} (hq : 1<q)
    (hres : (2:ℤ)^94517-1∣q-1) (hdiv : q∣3*(2:ℤ)^R) :
    ∃N : ℕ, 0<N ∧ q=((2:ℤ)^94517)^N ∧ 94517*N≤R :=
  (mersenne_radix_recovery (by omega) hq hres hdiv).2.2

example {d u : ℕ} (hd : 4≤d) (hres : (2:ℤ)^d-1∣(2:ℤ)^u-1) : d∣u :=
  mersenne_width_dvd (by omega) hres

#print axioms mersenne_power_remainder
#print axioms mersenne_not_dvd_three_power
#print axioms positive_divisor_two_power
#print axioms mersenne_width_dvd
#print axioms mersenne_base_recovery
#print axioms mersenne_radix_recovery
#print axioms adaptive_q_power_radix
#print axioms current_width_q_power_radix

end DiophantineConsistency.NativeAdaptiveMersenneChecks
