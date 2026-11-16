import IPRADerivations


/-! Axiom audit: every listed derivation uses only Lean's standard axioms
(`propext`, `Quot.sound`, `Classical.choice`), and no `sorryAx`. -/

#print axioms LeanProofs.IPRA.add_comm
#print axioms LeanProofs.IPRA.mul_assoc
#print axioms LeanProofs.IPRA.add_left_cancel
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.twoSquares
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.heronFactor
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.heron
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.lawOfCosines
#print axioms LeanProofs.IPRA.Algebra.CayleyHamilton.mul_adjugate
#print axioms LeanProofs.IPRA.Algebra.CayleyHamilton.det_mul
#print axioms LeanProofs.IPRA.Algebra.CayleyHamilton.cayleyHamilton2
#print axioms LeanProofs.IPRA.Algebra.CayleyHamilton.cayleyHamilton3
#print axioms LeanProofs.IPRA.Algebra.CayleyHamilton.leftMul_hom
#print axioms LeanProofs.IPRA.Algebra.CayleyHamilton.euler_four_squares
