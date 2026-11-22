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
