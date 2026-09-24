import Diophantine

/-!
Reproduce the transitive axiom audit for the recursively enumerable bridge
and the universal quartic by running:

    lake env lean Computability/HilbertTenthProblem/Lean/checks/RecursivelyEnumerableAxioms.lean

Every declaration below is expected to depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms. The printed audit
includes the independent vendor trace library, Mathlib's bounded evaluator,
and the concise CRT proof now used by the article-facing RE bridge.
-/

#print axioms PAListCoding.CipherOnes.onesCodes_dioph
#print axioms PAListCoding.CipherRelations.code_closed_of_ones
#print axioms PAListCoding.CipherRelations.constCode_fixed_closed_of_ones
#print axioms PAListCoding.CipherRelations.constCode_closed_of_ones
#print axioms PAListCoding.CipherRelations.indexCode_closed_of_ones
#print axioms PAListCoding.CipherRelations.mulRel_closed_of_ones
#print axioms PAListCoding.exactIter_iff_exists_sequence
#print axioms PAListCoding.exactIter_iff_exists_betaTrace
#print axioms PAListCoding.BoundedCipherDioph.boundedForall_dioph
#print axioms PAListCoding.IterationDioph.exactIter_dioph
#print axioms MRDP.boundedForall_dioph
#print axioms MRDP.primrec_diophFn
#print axioms MRDP.mrdp
#print axioms Nat.Partrec.Code.primrec_evaln
#print axioms Diophantine.boundedForall_dioph
#print axioms Diophantine.exactIter_dioph
#print axioms Diophantine.existsExactIter_dioph
#print axioms Diophantine.natPrimrec_dioph_comp
#print axioms Diophantine.natPrimrec_dioph
#print axioms Diophantine.encoded_evaln_natPrimrec
#print axioms Diophantine.rePred_dioph
#print axioms Jones1978.isDiophantine_of_rePred
#print axioms Jones1982.rePred_quartic58
#print axioms Jones1982.rePred_printed_systems
#print axioms Jones1982.rePred_theorem1_system
#print axioms Jones1982.rePred_theorem2_system
#print axioms Jones1982.rePred_theorem3_system
#print axioms Jones1982.rePred_quartic58_family
#print axioms Jones1982.UniversalQuartic.eval_jointPolynomial
#print axioms Jones1982.UniversalQuartic.eval_specialize
#print axioms Jones1982.UniversalQuartic.specialize_jointPolynomial
#print axioms Jones1982.UniversalQuartic.specialize_jointPolynomial_totalDegree
#print axioms Jones1982.universal_quartic58
