import DiophantineConsistency.GapNineRatio66

open DiophantineConsistency GapNineRatio66

-- Includes the power-of-two input b=1, where the population has no digit penalty.
example :
    (0+2200*(2*432007+12+2*0))+(139*(2*432007+12+2*0)-31*0-22) =
      2*(15*432007+79+1162*(2*432007+12+2*0)) := population_calibration 432007 0

example (b : ℕ) : threshold 432007 b = 2^6480184*(base 432007 b)^1162 := rfl

-- Only the small exponent arithmetic is normalized, never the enormous powers.
example (b : ℕ) : base 432007 b = 2^864026*b^2 := by
  simpa only [show 2*432007+12=864026 by decide] using base_eq 432007 b

example (a : ℕ) : base a 1=2^(2*a+12+2*0) := base_power rfl

#print axioms base_bounds
#print axioms base_eq
#print axioms size_bounds
#print axioms base_power
#print axioms blockLength_power
#print axioms threshold_power
#print axioms population_calibration
#print axioms rank_cast
#print axioms binomial_iff
#print axioms sound
#print axioms complete
