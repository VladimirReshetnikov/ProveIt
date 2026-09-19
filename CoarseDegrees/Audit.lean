import CoarseDegrees

/-!
  Axiom audit.  Run with `lake env lean CoarseDegrees/Audit.lean`.

  Fully proved theorems depend only on the standard axioms `propext`, `Classical.choice`,
  `Quot.sound`; theorems that use the admitted published results of
  `CoarseDegrees.Published` additionally show `sorryAx`.
-/

open CoarseDegrees

-- fully proved (no `sorryAx` expected)
#print axioms DensityZero.union
#print axioms CoarseEq.trans
#print axioms CoarseEq.ucEquiv
#print axioms UCRed.ncRed
#print axioms exists_computable_ncEquiv_iff
#print axioms no_least_of_two_witnesses
#print axioms no_least_of_trivial_core
#print axioms setCoarselyComputable_of_coarselyComputable
#print axioms graph_tRed
#print axioms computable_of_graph
#print axioms computable_of_core_trivial
#print axioms no_least_of_core_trivial
#print axioms exists_code_of_rePred
#print axioms oneGeneric_genericSet
#print axioms exists_oneGeneric
#print axioms rePred_range
#print axioms OneGeneric.not_setCoarselyComputable

-- report 10, combinatorial core: fully proved
#print axioms bridge
#print axioms exists_generic_pair
#print axioms HypIn.of_setTuringReducible
#print axioms not_setCoarseEq_of_ext
#print axioms tRed_graph
#print axioms sqrtBudget_densityZero
#print axioms leastClass_invariant
#print axioms SetCoarseEq.oddHalf
#print axioms SetCoarseEq.join
#print axioms blockCode_reducible
#print axioms Budget.inter
#print axioms densityBudget
#print axioms densityBudget_le

-- proved from the admitted published results (`sorryAx` expected)
#print axioms exists_hyp_minimal_pair
#print axioms exists_no_least_hyperdegree'
#print axioms exists_hyp_minimal_pair_close
#print axioms exists_no_least_hyperdegree_close
#print axioms no_cone_theorem
#print axioms leastClass_no_cone
#print axioms OneGeneric.no_least
#print axioms exists_re_no_least
#print axioms not_C1
#print axioms not_C1'
#print axioms not_C1Uniform
#print axioms not_C1Uniform'
#print axioms exists_binary_counterexample
