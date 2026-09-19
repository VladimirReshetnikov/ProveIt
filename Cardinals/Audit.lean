/-
  Axiom audit.  `lake env lean Cardinals/Audit.lean` prints, for each main theorem, the
  axioms it depends on.  Theorems of the combinatorial layer must show only the standard
  axioms `propext`, `Classical.choice`, `Quot.sound`; theorems that use the admitted
  published results additionally show `sorryAx`.
-/
import Cardinals

open Cardinals

-- fully proved (no `sorryAx` expected)
#print axioms FiniteCycles.no_equivariant_selectors
#print axioms OrdinalLemmas.strictMonoOn_image_eq_self
#print axioms Completeness.isComplete_succ_of_isSingular
#print axioms trace_reconstruction
#print axioms IsCompleteUF.succ_of_isSingular
#print axioms proj_OD
#print axioms sups_OD
#print axioms Ultraexacting.no_preserved_finite_family
#print axioms Ultraexacting.no_finite_valued_transversal
#print axioms Range.no_internal_unbounded_range
#print axioms ThirdRound.regressive_const_on_critical_sequence
#print axioms ThirdRound.phase_balance
#print axioms ThirdRound.tail_mean_indep
#print axioms countableCover_contra

-- proved from the admitted published results (`sorryAx` expected)
#print axioms barrier
#print axioms separation
#print axioms conditional_inconsistency
#print axioms no_CEx_above_extendible
#print axioms groundAxiom_obstruction
#print axioms general_ground_obstruction
#print axioms no_sandwich
#print axioms no_SC_above
#print axioms first_regularization
#print axioms projection_width
#print axioms no_smaller_exacting
