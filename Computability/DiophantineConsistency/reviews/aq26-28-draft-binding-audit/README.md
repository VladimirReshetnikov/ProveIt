# AQ28, AQ27 and AQ26 draft binding audit

The [observation](observation.json) records a bounded finite audit and source
hashes. The draft literal gates match the pinned candidate graphs, and the
residual vectors, folded sums, projected and reconstructed witness expressions,
transport-case indices and selected native wiring have additional syntactic
checks. Isolated regeneration reproduces the current draft files and negative
controls reject altered maps, residuals, deleted equations, native wiring,
parent templates and the original AQ28 arity error.

The original AQ28 `sum_zero` statement incorrectly quantified over `Fin 18`
instead of `Fin 19`, due to overlapping textual substitutions. The generator
and draft have been corrected. These checks do not compile Lean, validate the
entire positivity or transport proofs, or prove native iPRA equivalence. The
selected model/native wiring checks are textual and are not a full Lean parser.

A single bounded, low-priority [mixed-provider AQ28 syntax probe](exploratory-probe.json)
did not produce an elaboration result. Its first invocation exited 1 because
an empty local namespace shadowed the historical parent; its corrected
invocation timed out after 30 seconds with exit 124. No output object was
present afterward. This deliberately mixed historical-project/new-Foundation
probe cannot establish provider compatibility or any theorem.
