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
