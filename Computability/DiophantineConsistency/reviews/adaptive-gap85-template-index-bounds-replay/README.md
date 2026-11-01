# Restricted template index bounds

Independent author and peer both PASS with identical source, object, and full-log hashes for two modules. The checks report only the standard Lean axioms. The input and replay driver are `research/adaptive-gap85-normalization/TemplateIndexBounds.lean` and `replay_index_bounds.py`. Direct Mathlib objects are guarded; package-transitive ancestry is inherited.

The integer theorem concludes the second Pell index only for the explicitly stated special template, positivity conditions, and assumed index trichotomy. It does not construct a representative for an arbitrary 85-zero, prove the trichotomy in arbitrary models, or establish an 85-operation equivalence.
