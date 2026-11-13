import DiophantineConsistency.ArithmeticGcdNormalization
import DiophantineConsistency.ArithmeticSquareDivisibility

/-! Unchecked draft: elementary IΣ₁-model divisibility for the 72 carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticGcdNormalization ArithmeticSquareDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- From `q³ ∣ 3h`, recover `q ∣ h` without prime factorization. -/
theorem dvd_of_cube_dvd_three (q h : V)
    (hd : q*q*q ∣ 3*h) : q ∣ h := by
  obtain ⟨d, hd⟩ := hd
  have hq3 : q ∣ 3*h := ⟨q*q*d, by rw [hd]; ring⟩
  have hr : q % 3 < (3:V) := mod_lt q (by norm_num)
  have hrle : q % 3 ≤ (2:V) := by
    apply lt_succ_iff_le.mp
    simpa using hr
  have hdiv := div_add_mod q 3
  by_cases h0 : q % 3 = 0
  · have hqeq : q = 3*(q/3) := by rw [h0, add_zero] at hdiv; exact hdiv.symm
    refine ⟨(q/3)*q*d, ?_⟩
    apply mul_left_cancel₀ (show (3:V) ≠ 0 by norm_num)
    calc
      3*h = q*q*q*d := hd
      _ = 3*(q*((q/3)*q*d)) := by rw [hqeq]; ring
  · have hrpos : 0 < q % 3 := lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm h0)
    have hrone : 1 ≤ q % 3 := pos_iff_one_le.mp hrpos
    by_cases h1 : q % 3 = 1
    · have hqeq : q = 3*(q/3)+1 := by rw [h1] at hdiv; exact hdiv.symm
      have hbez : Bez (3:V) q 1 := ⟨q/3, 0, 0, 1, by rw [hqeq]; ring⟩
      exact unit_certificate_cancel hbez hq3
    · have hgt : 1 < q % 3 := lt_of_le_of_ne hrone (Ne.symm h1)
      have htwo : (2:V) ≤ q % 3 := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hgt
      have h2 : q % 3 = 2 := le_antisymm hrle htwo
      have hqeq : q = 3*(q/3)+2 := by rw [h2] at hdiv; exact hdiv.symm
      have hbez : Bez (3:V) q 1 := ⟨0, 1, q/3+1, 0, by rw [hqeq]; ring⟩
      exact unit_certificate_cancel hbez hq3

/-- The positive-square carrier gives divisibility by its scale. -/
theorem scale_dvd_carrier (U D N : V) (hU : 0 < U)
    (hm : D*D = U*U*N) : U ∣ D := by
  apply dvd_of_square_dvd U D hU
  exact ⟨N, hm⟩

#print axioms FreeMainDivisibility.dvd_of_cube_dvd_three
#print axioms FreeMainDivisibility.scale_dvd_carrier
end FreeMainDivisibility
