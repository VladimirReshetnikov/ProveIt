import DiophantineConsistency.NativeArithmetic52

open DiophantineConsistency.NativeArithmetic52

#print axioms restrict_lift
#print axioms lift_zero_iff
#print axioms eq_lift_of_zero
#print axioms source_zero_iff
#print axioms exists_zero_iff
#print axioms exists_positive_zero_iff

-- The ordinary strong multiplier is explicit, without a discriminant factor.
example (ports : Fin 4 → ℤ) (v : Fin 16 → ℤ) :
    (registers ports v).I = (registers ports v).c * (registers ports v).c * v 6 := rfl

-- The native q-cubed scale is recovered by the defining register equations.
example (ports : Fin 4 → ℤ) (v : Fin 16 → ℤ) :
    (registers ports v).N = (registers ports v).q ^ 3 := by
  change (1+v 0*ports 0)*(1+((1+v 0*ports 0)*(1+v 0*ports 0)-1)) =
    (1+v 0*ports 0)^3
  ring
