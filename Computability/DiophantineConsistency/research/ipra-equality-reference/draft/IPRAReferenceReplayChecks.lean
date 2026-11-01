import DiophantineConsistency.IPRAReferenceAQ29Direct
import DiophantineConsistency.IPRAReferenceRoundtrip

/-! Uncompiled joint replay target. A passing guarded replay must bind these
four exact report names as well as its complete source and object ancestry. -/
#print axioms DiophantineConsistency.IPRAReferenceAQ29Direct.literal_equivalence
#print axioms DiophantineConsistency.IPRAReferenceRoundtrip.provability_iff
#print axioms DiophantineConsistency.IPRAReferenceInductionConversion.nativeToReference
#print axioms DiophantineConsistency.IPRAReferenceRefutationReading.refutation_eq_erased_native
