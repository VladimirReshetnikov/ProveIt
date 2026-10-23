import DiophantineConsistency.SplitCircuitSteps59
open DiophantineConsistency.SplitCircuitSteps59
#print axioms natural_step_36
#print axioms natural_step_279
#print axioms natural_step_514
#print axioms natural_power_402
#print axioms natural_power_407

-- Power sharing is valid in every characteristic, including the polynomial ring.
example {R : Type*} [CommRing R] (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 402 = naturalRegister p x 36 ^ 2279 :=
  natural_power_402 p x
