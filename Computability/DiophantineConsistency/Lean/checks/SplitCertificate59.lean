import DiophantineConsistency.SplitCertificate59

open DiophantineConsistency.SplitCertificate59

#print axioms weights_injective
#print axioms active_isolated
#print axioms linear_cross
#print axioms quadratic_cross
#print axioms transformed_zero_iff
#print axioms delivered_zero_iff
#print axioms rowValue_eq_source
#print axioms coeff_source_rows
#print axioms coeff_zero_iff_source_zero

example : weights 20 = 116 := rfl
example : targets 21 = 2129 := rfl
example : rowOrder 3 = 14 := rfl

-- The authoritative source has the old positive transport coordinate.
example (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) :
    sourceRows ports x 14 =
      (ports 1+x 10)*(1+x 0*ports 0-x 1-x 2)+(1+x 0*ports 0-x 1)-
        x 3*(x 0*ports 0)-1 := by
  change ((ports 1) + x 10 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + (ports 0) * (x 0 * x 10) + ((-(ports 0))) * (x 0 * x 3)) = _
  ring
