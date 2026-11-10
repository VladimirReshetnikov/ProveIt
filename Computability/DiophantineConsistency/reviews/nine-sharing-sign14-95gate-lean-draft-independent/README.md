# Independent source-only review

PASS for structural correspondence. A separate restricted parser expanded all audited staged shared definitions and the seven optimized shared definitions, parsed the two optimized local-let rows, and compared all five expanded Lean draft row ASTs exactly with the independently reviewed external 95-gate candidate. It checked the four rewritten rows, unchanged row01, all seven changed shared dependencies, source hashes, the five-square seed layout, and the presence of generic `[CommRing R]` row/seed evaluation-equality statements. The external two ring rewrites and staged source provider audits were replayed.

This is not a Lean prelaunch or proof. The source has not been elaborated: imports, tactic success, cast simplification and generic-ring proofs remain unverified. Exact external AST correspondence is an independent Python observation, not a Lean JSON/file binding; degree/iPRA transfer for the optimized expression remains separate.
