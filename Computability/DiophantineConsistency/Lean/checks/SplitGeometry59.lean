import DiophantineConsistency.SplitGeometry59

open DiophantineConsistency.SplitCertificate59

#print axioms weights_injective
#print axioms targets_injective
#print axioms active_isolated
#print axioms linear_cross
#print axioms quadratic_cross
#print axioms inputPositions_card
#print axioms targetPositions_card
#print axioms inputPositions_range
#print axioms targetPositions_range

example : inputPositions.card = 31 := inputPositions_card
example : targetPositions.card = 22 := targetPositions_card
example : inputPositions ⊆ Finset.range 117 := inputPositions_range
example : targetPositions ⊆ Finset.range 2162 := targetPositions_range
example : 0 ∉ inputPositions := inputPositions_zero
