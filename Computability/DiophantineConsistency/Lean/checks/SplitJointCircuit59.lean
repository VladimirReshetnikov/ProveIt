import DiophantineConsistency.SplitJointCircuit59
open DiophantineConsistency.SplitJointCircuit59
#print axioms variableNames_injective
#print axioms fixedNames_injective
#print axioms positive_topological
#print axioms positive_all_live
#print axioms positive_operation_count
#print axioms positive_live_operation_count
#print axioms positive_all_inputs
#print axioms positive_all_fixed
#print axioms positive_named_indices
#print axioms eval_positivePolynomial
#print axioms positiveValue_map
#print axioms natural_topological
#print axioms natural_all_live
#print axioms natural_operation_count
#print axioms natural_live_operation_count
#print axioms natural_all_inputs
#print axioms natural_all_fixed
#print axioms natural_named_indices
#print axioms eval_naturalPolynomial
#print axioms naturalValue_map

example : positiveNodes.length = 491 := positive_length
example : naturalNodes.length = 498 := natural_length
example : DiophantineConsistency.ArithmeticDAG.liveOperationCount positiveNodes positiveOutput = 456 :=
  positive_live_operation_count
example : DiophantineConsistency.ArithmeticDAG.liveOperationCount naturalNodes naturalOutput = 463 :=
  natural_live_operation_count
example : variableNames 7 = "j" := rfl
example : fixedNames 10 = "base_scale" := rfl
example : fixedNames 11 = "threshold_scale" := rfl
