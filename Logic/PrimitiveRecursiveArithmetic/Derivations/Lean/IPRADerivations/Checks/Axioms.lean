import IPRADerivations.Geometry.TriangleFormulas

/-! Axiom audit: every listed derivation uses only Lean's standard axioms
(`propext`, `Quot.sound`, `Classical.choice`), and no `sorryAx`. -/

#print axioms LeanProofs.IPRA.add_comm
#print axioms LeanProofs.IPRA.mul_assoc
#print axioms LeanProofs.IPRA.add_left_cancel
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.twoSquares
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.heronFactor
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.heron
#print axioms LeanProofs.IPRA.Geometry.TriangleFormulas.lawOfCosines
