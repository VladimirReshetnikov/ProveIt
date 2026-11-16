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
#print axioms LeanProofs.IPRA.Geometry.EulerRodrigues.rodrigues_orthogonal
#print axioms LeanProofs.IPRA.Geometry.EulerRodrigues.rodrigues_det
#print axioms LeanProofs.IPRA.Geometry.EulerRodrigues.rodrigues_axis
#print axioms LeanProofs.IPRA.Geometry.EulerRodrigues.adjugate_shift
#print axioms LeanProofs.IPRA.Geometry.EulerRodrigues.det_shift_formula
#print axioms LeanProofs.IPRA.Geometry.EulerRodrigues.adjugate_adjugate
#print axioms LeanProofs.IPRA.Geometry.Projective.double_cross
#print axioms LeanProofs.IPRA.Geometry.Projective.desargues_identity
#print axioms LeanProofs.IPRA.Geometry.Projective.plucker_relation
#print axioms LeanProofs.IPRA.Geometry.Projective.pappus
#print axioms LeanProofs.IPRA.Geometry.SphericalTrigonometry.binet_cauchy
#print axioms LeanProofs.IPRA.Geometry.SphericalTrigonometry.gram_identity
#print axioms LeanProofs.IPRA.Geometry.SphericalTrigonometry.cosine_law
#print axioms LeanProofs.IPRA.Geometry.SphericalTrigonometry.lagrange_identity
#print axioms LeanProofs.IPRA.Algebra.PolynomialFormulas.quadratic
#print axioms LeanProofs.IPRA.Algebra.PolynomialFormulas.cardano
#print axioms LeanProofs.IPRA.Algebra.PolynomialFormulas.ferrari
#print axioms LeanProofs.IPRA.Algebra.PolynomialFormulas.triple_angle
#print axioms LeanProofs.IPRA.DiophantineNumberTheory.Identities.quintic_power
#print axioms LeanProofs.IPRA.DiophantineNumberTheory.Identities.quintic_norm
#print axioms LeanProofs.IPRA.DiophantineNumberTheory.Identities.pythagorean_parametrisation
#print axioms LeanProofs.IPRA.DiophantineNumberTheory.Identities.fermat_triangle
#print axioms LeanProofs.IPRA.DiophantineNumberTheory.Pell.brahmagupta
#print axioms LeanProofs.IPRA.DiophantineNumberTheory.Pell.composition
#print axioms LeanProofs.IPRA.Foundations.QuantitativeIdentities.product_contract
#print axioms LeanProofs.IPRA.Foundations.QuantitativeIdentities.cubic_difference
#print axioms LeanProofs.IPRA.Foundations.QuantitativeIdentities.pow_difference
#print axioms LeanProofs.IPRA.Foundations.QuantitativeIdentities.geometric_sum
#print axioms LeanProofs.IPRA.Foundations.QuantitativeIdentities.zeta_zeros_cosine
#print axioms LeanProofs.IPRA.Foundations.QuantitativeIdentities.circle_parametrisation
#print axioms LeanProofs.IPRA.Geometry.Morley.trisector_identity
#print axioms LeanProofs.IPRA.Sums.gauss
#print axioms LeanProofs.IPRA.Sums.odd_sum
#print axioms LeanProofs.IPRA.Sums.telescope
#print axioms LeanProofs.IPRA.Sums.abel_summation
