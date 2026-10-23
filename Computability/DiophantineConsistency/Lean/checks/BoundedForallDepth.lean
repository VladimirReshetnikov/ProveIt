import DiophantineConsistency.BoundedForallDepth

open DiophantineConsistency

example : BoundedForallSize.certificateCost 0 0 0 = 20694 := by
  rw [BoundedForallDepth.certificateCost_eq]

#print axioms BoundedForallDepth.certificateCost_eq
#print axioms BoundedForallDepth.boundedForall_witnessCount
#print axioms BoundedForallDepth.pow_depth
#print axioms BoundedForallDepth.binomial_depth
#print axioms BoundedForallDepth.factorial_depth
#print axioms BoundedForallDepth.product_depth_le
#print axioms BoundedForallDepth.finiteRep_depth_le
#print axioms BoundedForallDepth.boundedForall_depth_le
