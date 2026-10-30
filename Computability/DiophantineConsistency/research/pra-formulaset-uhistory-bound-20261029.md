# Formula-set bounds with universal-formula histories

`PRAFormulaSetUHistoryBound` composes the positive formula-set bound with the actual Foundation `isUFormula` fixpoint graph. It establishes a closed candidate-PRA sentence by proving its matrix in every IOpen model and applying completeness. The proof uses the explicit negative-bit majorant for the enclosing formula set and the positive-bit majorant inside the universal-formula fixpoint.

For each relevant formula index, the sentence assumes a sequence code below the common bound, a bound on that sequence's positive bit graph, a membership witness for the index, and the bounded actual `limSeqDef` graph. It also assumes the separately bounded BV graph at witness zero. These hypotheses replace the previously opaque bounded `isUFormula` subgraph, but no construction of their witnesses is provided.

The result therefore does not bound the recursive history itself, does not discharge the BV graph obligation, and does not provide a complete ZFC refutation certificate or an HA proof. The focused replay and its exact source and object authentication are recorded in `reviews/pra-formulaset-uhistory-bound-author-replay`.
