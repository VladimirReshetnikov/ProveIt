import DiophantineConsistency.SplitKernelData59
open DiophantineConsistency.SplitKernelData59
#print axioms degree_D0
#print axioms degree_D1
#print axioms degree_D2
#print axioms leading_D2
#print axioms kernelBounds_of_records
#print axioms records0_lt
#print axioms records1_lt
#print axioms records2_lt
#print axioms kernelBounds_box
example : positions1 6 = 383 := rfl
example (ports : Fin 4 → ℤ) : coefficients1 ports 6 = 2*ports 0*(ports 1+1) := by
  change 2*ports 0+2*ports 0*ports 1 = 2*ports 0*(ports 1+1)
  ring
example (ports : Fin 4 → ℤ) : (D2 ports).coeff 1929 = 1 := leading_D2 ports
