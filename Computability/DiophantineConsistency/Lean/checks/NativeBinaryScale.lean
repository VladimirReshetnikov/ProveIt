import DiophantineConsistency.NativeBinaryScale

open DiophantineConsistency.NativeBinaryScale

example : (5 : ℕ) ∣ 15 := width_dvd_exponent (by decide) (by decide)

#print axioms sourceQ_cast
#print axioms source_X_eq_q_mul
#print axioms source_q_power_two
#print axioms width_dvd_exponent
#print axioms source_q_power_radix
