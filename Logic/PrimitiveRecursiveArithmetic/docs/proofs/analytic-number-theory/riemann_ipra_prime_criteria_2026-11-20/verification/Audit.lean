import RiemannIPRA
open RiemannIPRA LeanProofs.ConciseIPRA
#check RH
#check GRH
#check ERH
#check RiemannIPRA.erh_implies_grh
#check RiemannIPRA.grh_implies_rh
#check RiemannIPRA.erh_iff_no_counterexample
#print axioms RiemannIPRA.erh_implies_grh
#print axioms RiemannIPRA.erh_iff_no_counterexample
#print axioms RiemannIPRA.naturalTerms_sound
#print axioms RiemannIPRA.erh_reading
#print axioms PacketLanguage.value_program
#print axioms PacketLanguage.value_primeCode

-- Internal derivations in the first-order intuitionistic theory
#check PacketAudit.rh_iff
#check PacketAudit.grh_iff
#check PacketAudit.erh_iff
#check PacketAudit.erh_counter_iff_first
#check PacketSlack.rh_iff_cert
#check PacketSlack.grh_iff_cert
#check PacketSlack.erh_iff_cert
#print axioms PacketAudit.erh_iff
#print axioms PacketAudit.erh_counter_iff_first
#print axioms PacketSlack.erh_iff_cert
#print axioms Lagarias.upper_no_counterexample

-- Interpretations of literal object-language formulas
#check RiemannIPRA.Discrete.statement_equivalent
#check RiemannIPRA.Sparse.sparse_sentence_iff
#print axioms RiemannIPRA.Discrete.statement_equivalent
#print axioms RiemannIPRA.Sparse.sparse_sentence_iff

-- Additional closed arithmetic sentences and finite algebraic theorems
#check PrimeForms.allPackets
#check PrimeForms.witness
#check MertensSyntax.progressionGRH
#check DivisorMatrices.ERH
#check FareyEnergy.cyclotomicGRH
#check DyadicSeries.statement
#check FareyRH.GRH
#check Lagarias.upperRH
#check Lagarias.strictRH
#check MatrixIdentity.masked_determinant
#check EnergyInequality.jordanPairs_eq
#check EnergyInequality.jordan_quarter
#check EnergyInequality.jordan_inverse_mass
#check EnergyInequality.recover_eight
#check AbelIdentity.recover
#print axioms MatrixIdentity.masked_determinant
#print axioms EnergyInequality.jordan_quarter
#print axioms AbelIdentity.recover

-- New closed forms, internal derivations, and interpreted arithmetic tests
#check CubeTests.rh_cube
#check CubeTests.grh_cube
#check CubeTests.erh_cube
#check CubeTests.schedule_iff
#check CubeTests.failure_iff
#check CubeTests.failure_iff_first_radius
#print axioms CubeTests.failure_iff_first_radius
#print axioms CubeTests.diagonal_iff
#check RiemannIPRA.ProductCertificate.rh_iff
#check RiemannIPRA.ProductCertificate.grh_iff
#check RiemannIPRA.ProductCertificate.erh_iff
#print axioms RiemannIPRA.ProductCertificate.erh_iff
#check RiemannIPRA.SymmetricPrefixes.statement_iff
#check RiemannIPRA.CoefficientTest.coefficients_iff
#check RiemannIPRA.CoefficientTest.grid_iff
#print axioms RiemannIPRA.SymmetricPrefixes.statement_iff
#print axioms RiemannIPRA.CoefficientTest.coefficients_iff
#check RiemannIPRA.SplitPrimes.split_iff
#check RiemannIPRA.SplitPrimes.rh_reading
#check RiemannIPRA.SplitPrimes.grh_reading
#check RiemannIPRA.SplitPrimes.unary_grh_iff
#check RiemannIPRA.SplitPrimes.unary_erh_reading
#check RiemannIPRA.SplitPrimes.erh_reading
#check RiemannIPRA.SplitPrimes.prog_grh_to_rh
#check RiemannIPRA.SplitPrimes.linear_field_log
#print axioms RiemannIPRA.SplitPrimes.unary_grh_iff
#print axioms RiemannIPRA.SplitPrimes.unary_erh_reading
#print axioms RiemannIPRA.SplitPrimes.prog_grh_to_rh
#check RiemannIPRA.Taylor.statement
#check RiemannIPRA.Taylor.numerator_reading
#check RiemannIPRA.Taylor.statement_reading
#check RiemannIPRA.Taylor.full_to_diagonal
#check RiemannIPRA.Taylor.diagonal_to_lacunary
#print axioms RiemannIPRA.Taylor.statement_reading
#check PowerDivisorSyntax.statement
#check PowerDivisorBounds.power_divisor_transfer
#check PowerDivisorInversion.act_mul
#check PowerDivisorInversion.growth_iff
#check PowerDivisorInversion.uniform_growth_iff
#check LiouvilleCriterion.mertens_iff_liouville
#print axioms PowerDivisorInversion.uniform_growth_iff
#print axioms LiouvilleCriterion.mertens_iff_liouville

#check RiemannIPRA.SplitPrimes.split_iff_no_irred_divisor
#print axioms RiemannIPRA.SplitPrimes.split_iff_no_irred_divisor
#check RiemannIPRA.UniversalCriteria.taylorScheduled
#check RiemannIPRA.UniversalCriteria.taylorFirstFailure
#check RiemannIPRA.UniversalCriteria.splitFirstFailure
#check RiemannIPRA.UniversalCriteria.symmetricScheduled
#print axioms RiemannIPRA.UniversalCriteria.taylorFirstFailure
