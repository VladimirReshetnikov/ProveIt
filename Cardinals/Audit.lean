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
#print axioms Countable.zero_one
#print axioms Countable.Cantor.global_fixed_point
#print axioms Countable.Klein.separation
#print axioms RelWitness.jOrd_nat
-- Kunen-free facts (no `sorryAx` expected): they hold for virtual witnesses too
#print axioms RelWitness.jv_subset_fixed
#print axioms RelWitness.no_surj_pow_crit
#print axioms RelWitness.slSem_critSeq
#print axioms RelWitness.crit_regular
#print axioms RelWitness.jOrd_omega
#print axioms interleave
#print axioms RelWitness.trace_fixed_of
#print axioms FourthRound.finiteChange_realize_insert
#print axioms FourthRound.shift_ne
#print axioms FourthRound.no_finite_invariant
#print axioms FourthRound.residue_law
#print axioms Bridge.realize_toLex
#print axioms RelWitness.definable_fixed
#print axioms RelWitness.le_jOrd
#print axioms card_sUnion_le

-- proved from the admitted published results (`sorryAx` expected)
#print axioms barrier
#print axioms separation
#print axioms conditional_inconsistency
#print axioms no_CEx_above_extendible
#print axioms groundAxiom_obstruction
#print axioms general_ground_obstruction
#print axioms no_sandwich
#print axioms RelWitness.strongLimit
#print axioms not_REx_shortCofinal
#print axioms le_of_CEx
#print axioms no_SC_above
#print axioms RelWitness.fixed_small_subset
#print axioms RelWitness.no_small_fixed_family
#print axioms RelWitness.orb_mem_X
#print axioms RelWitness.jv_orb
#print axioms RelWitness.zero_or_full
#print axioms RelWitness.regressive_const
#print axioms first_regularization
#print axioms projection_width
#print axioms no_smaller_exacting
