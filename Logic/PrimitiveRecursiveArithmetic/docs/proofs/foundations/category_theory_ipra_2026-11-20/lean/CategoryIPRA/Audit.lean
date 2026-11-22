import CategoryIPRA

/-!
Run after a successful build:

  lake env lean CategoryIPRA/Audit.lean

The generated audit output must be inspected; no audit transcript is asserted
to have been produced in the generation environment.
-/

#print axioms CategoryIPRA.Representability.represented_faithful
#print axioms CategoryIPRA.LocalYoneda.local_yoneda
#print axioms CategoryIPRA.Representability.representable_inverse_left
#print axioms CategoryIPRA.Representability.representable_inverse_right
#print axioms CategoryIPRA.Density.generator_roundtrip
#print axioms CategoryIPRA.Density.reindex_value
#print axioms LeanProofs.IPRA.Foundations.Yoneda.yoneda_closed
