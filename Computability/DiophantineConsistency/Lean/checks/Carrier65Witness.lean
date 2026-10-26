import DiophantineConsistency.Carrier65Witness

open DiophantineConsistency

-- The port assumptions apply to the source mask once, without a second shift.
example : Carrier65Witness.PortBounds ![31, 29, 1, 32] := by
  constructor <;> decide

#print axioms Carrier65Witness.positive_zero_rank_window
#print axioms Carrier65Witness.positive_zero_restores_index
#print axioms Carrier65Witness.polynomial_zero_restores_index
