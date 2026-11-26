/-
# Existing-source theorem audit (UNBUILT in the producing environment)

This generated file imports the three extracted source targets and asks Lean
to display types and axiom dependencies of selected EXISTING theorems.
It contains no formalization of the new results in the accompanying paper.
Upstream: lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207.
-/

import New.Congruences.Selmer.GeneralTheorem
import Lib.Cyclotomic.OddSha
import New.Reduction.Lattices.TwistedLattice

#check New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add
#print axioms New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add

#check New.Selmer.exists_rootsOfUnity_ellVal_eval_le
#print axioms New.Selmer.exists_rootsOfUnity_ellVal_eval_le

#check New.Selmer.exists_anticyclotomic_twist
#print axioms New.Selmer.exists_anticyclotomic_twist

#check New.exists_length_shaOdd_le
#print axioms New.exists_length_shaOdd_le

#check New.TwistedLattice.covolume_add_index_nonneg
#print axioms New.TwistedLattice.covolume_add_index_nonneg
