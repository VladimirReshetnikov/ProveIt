import DiophantineConsistency.ObjectUnpair

open DiophantineConsistency SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

example : ObjectPairingSyntax.expression.toPolynomial.totalDegree≤4 :=
  ObjectPairingSyntax.expression_degree
example : BProv ZFCax_s [] ObjectPairingGraph.totalForm := ObjectPairingGraph.zfc_proves_total
example : BProv ZFCax_s [] ObjectPairingGraph.uniqueForm := ObjectPairingGraph.zfc_proves_unique
example : BProv ZFCax_s [] ObjectPairingSurjective.surjectiveForm :=
  ObjectPairingSurjective.zfc_proves_surjective
example {V : Type} {mem : V → V → Prop} (H : ZFAxioms mem)
    (z : ObjectOmegaSemiring.Natural H) :
    ∃ a b : ObjectOmegaSemiring.Natural H,z=ObjectNatPairing.pair H a b :=
  ObjectPairingSurjective.pair_surjective H z

#print axioms ObjectNaturalDiscrete.zero_or_add_one
#print axioms ObjectNaturalDiscrete.add_one_ne_zero
#print axioms ObjectNaturalDiscrete.lt_iff_exists_add_one
#print axioms ObjectNaturalDiscrete.mul_self_eq_self_iff
#print axioms ObjectNaturalDiscrete.cast_lt_cast
#print axioms ObjectNatPairing.certificate_sound
#print axioms ObjectNatPairing.certificate_complete
#print axioms ObjectNatPairing.exists_certificate_iff
#print axioms ObjectNatPairing.pair_cast
#print axioms ObjectPairingSyntax.rows_zero_iff
#print axioms ObjectPairingSyntax.expression_degree
#print axioms ObjectPairingSyntax.expression_zero_iff
#print axioms ObjectPairingSyntax.exists_expression_zero_iff
#print axioms ObjectPairingSyntax.exists_equationRel_iff
#print axioms ObjectPairingGraph.graphForm_naturals
#print axioms ObjectPairingGraph.graphForm_spec
#print axioms ObjectPairingGraph.sentence_totalForm
#print axioms ObjectPairingGraph.sentence_uniqueForm
#print axioms ObjectPairingGraph.zfc_proves_total
#print axioms ObjectPairingGraph.zfc_proves_unique
#print axioms ObjectPairingSurjective.pair_successor
#print axioms ObjectPairingSurjective.pair_surjective
#print axioms ObjectPairingSurjective.sentence_surjectiveForm
#print axioms ObjectPairingSurjective.zfc_proves_surjective
#print axioms ObjectPairingInjective.pair_eq_pair_iff
#print axioms ObjectUnpair.pair_unpair
#print axioms ObjectUnpair.unpair_pair
#print axioms ObjectUnpair.unpair_zero
#print axioms ObjectUnpair.unpair_eq_iff
#print axioms ObjectUnpair.unpair_cast
#print axioms ObjectUnpair.pairEquiv
#print axioms ObjectUnpair.sentence_inverseUniqueForm
#print axioms ObjectUnpair.zfc_proves_inverse_unique
