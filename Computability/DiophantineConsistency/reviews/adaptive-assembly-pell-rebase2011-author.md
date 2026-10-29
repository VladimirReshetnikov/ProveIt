# Pell prerequisites after the half-index refactor

An author replay passed the two Assembly Pell prerequisites affected by the updated HalfBinomial source: `ArithmeticOuterSeed` and `ArithmeticConstructionBoundPell`. The replay uses the half-index author provider and four independently accepted SquaredSeed/AuxiliarySeed objects and checks. Independent replay at `/tmp/adaptive13-assembly-pell-rebase-mzg0079p` passed against the independently replayed half-index provider; both source, object and complete-log hashes match the author run.

The seed audit traverses the DiophantineConsistency source closure of those four reused objects. It confirms that neither changed HalfBinomial nor AdaptivePopulation is in that closure, and checks all 14 inherited source hashes and the corresponding old/new object hashes before reuse. The driver grafts only the four checked seed/check objects, excludes the two affected old outputs, snapshots the current target sources, and reauthenticates sources and selected objects at completion. Cross-namespace and package internals remain inherited boundaries.

Both target modules exited successfully without diagnostics. The [14-file author evidence manifest](adaptive-assembly-pell-rebase2011-author-evidence/FILES.json) has SHA256 `70497ba8af4249d36c68767605a192045eda404a70ee3fa6671e7fb234f8e37c`; it includes the driver, dependency audit, source snapshots, logs, timings, and provider metadata. The author provider is `/tmp/adaptive13-assembly-pell-rebase-ptmu6_9s/lib`.

This is a partial prerequisite replay, not a completed CellWindow continuation, full current Assembly build, or syntactic HA proof.
