# Final adversarial novelty review

Comparison cutoff: `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`. No later refresh is included.

## Disposition

All four candidates remain defensible as narrowly stated. Their claimed contribution must be the residual obligation described below. Rebuilding previously proposed abstractions earns no novelty or extra savings.

### A. Consume the supplied program certificate

Assume packet i's `fun_prop` automation and packet e's shared program builders already exist. The second extensional certificate route still remains: private primitive-recursion facts for the record-state enumerator establish `pr_boundedRun`, then establish public computability facts independently of the supplied scalar realizer. A deletes that route by deriving `haltingTest_natPrimrec` from `DirectEnumerator.program` and the existing `ScalarPRCode.primrec`.

A must also rebase `refutationInputs_re` onto the scalar test and the retained semantic halting equivalence. Otherwise its old direct use of `pr_boundedRun` would prevent deletion. The supplied migration does this. The actual program, its realization proof, the generic soundness theorem `ScalarPRCode.primrec`, the executable test, and the semantic halting bridge remain. Splitting the lower semantic module is plumbing for the deletion, not another idea.

Use: “Remove a redundant certification route after the previously proposed automation is available.”

Avoid: “Replace 213 lines of repeated composition proofs after all earlier ideas.” The 213 figure is only a static raw-baseline difference: the three-file model has 608 versus 395 physical lines, including its new module and import change. It is neither a measured post-adoption saving nor evidence that the production import closure compiles. The prior fun_prop proposal already shortens much of that raw composition syntax.

### B. Prove the exact safe mutation by boundary conservation

Assume cyclic telescoping, top-field reset/local scan APIs, finite update identities, convolution linearity, and point-mass APIs are already available. Do not present any of those as new.

The residual argument is specific: the physically interior dummy perturbation has all of its kernel and temporal exponents below the word length, so its ordinary raw-word increment is exactly `(K+2^W)*delta`. The old and updated assembled words have the same terminal carry (in this case zero). The already-available exact telescope therefore transfers that raw increment to the normalized words. This discharges the actual ordinary mutation equality without using the separate coarse numerical estimates of K, F, and delta.

The distinction is not “nonwrapping is unnecessary.” Spatial and temporal placement conditions still ensure the perturbation support does not wrap. Zero boundary carry still uses Boolean controls, nonzero cell count, and whole-cell displacement. The new endpoint changes the proof route to the existing safe equality, not the theorem's admissible updates.

Use: “Remove the coarse magnitude-bound chain from the proof dependency of safe_normalized_increment, by exact perturbation support and equal-boundary-carry cancellation.”

Avoid: “Invent exact telescoping,” “remove all nonwrapping assumptions,” or “delete 100 lines.” The production cyclic/support adapters remain to be implemented. Public quantitative declarations also have check clients in CurrentDummySafety2011Checks.lean: kernel_upper_bound, safe_increment_bound, and safe_increment_div_bound. Decide explicitly whether to preserve them or retire those standalone checks; their entire text cannot be credited as saved under blanket API preservation. normalized_nonwrap_of_safe itself can be recovered later as a consequence of the new equality and a strict bound on the new normalization, avoiding circularity.

The old reports explicitly leave this numerical obligation in place: zn C retains F+A*delta<modulus; zp says its translate argument does not remove the safety premises; zq composes the existing safe one-dummy theorem.

### C. Use the joint discrete numerator envelope

The accepted incremental content is the particular tighter envelope for the actual shifted numerator,
`Qstar <= (4*A-4)*D+1`,
and its denominator domination identity. It is not general polynomial-majorant automation or a new invocation of nlinarith. The exact-signature proof replaces a 39-line theorem by 29 lines with no added production helpers/imports. That is a local raw-source measurement with checked standalone proof, not a complete production-module build or a global post-adoption saving. The independent corpus audit found no earlier proposal of this particular joint W,C envelope.

### D. Optional constant-predicate endpoint

D is compatible with A but is not required for A. A already removes the private Primrec subgraph while preserving an actual-enumerator proof of refutationInputs_re. D substitutes a classical proof only at that last REPred endpoint. Conversely, applying D alone does not remove the private Primrec layer, because haltingTest_natPrimrec still needs it until A is adopted.

Do not add D's old-baseline 10-line diff to A's 213. They both modify refutationInputs_re, and a combined candidate needs D rebased onto A. There is no second claim to delete the enumerator, semantic bridge, or full Computability module. Merely changing the proof also does not remove its module imports; a dependency-reduction claim needs an actual separate import migration.

Use: “An optional shorter classical proof of the fixed constant predicate's REPred endpoint, while retaining the supplied enumerator as the effective construction.”

Keep the provenance docstring correction. No uniform algorithm in P, effective consistency decision, concrete equation extraction, or changed explicit program follows. The proof-irrelevance observation applies only when a choice-defined polynomial changes proof arguments of exactly the same proposition; it is a compatibility fact, not an algorithm.

## Best pinned prior-artifact anchors

All links below use the final comparison cutoff, including relocated original incoming packets.

- **A / automation already assumed:** [packet i checker notes, lines 32–58](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26i/notes/checker.md#L32-L58). It automates extensional Primrec proofs and expressly leaves program syntax and realizers intact.
- **A / builder sharing already assumed:** [packet e report, lines 355–364](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex#L355-L364). It shares direct/native graph-enumerator control templates while preserving different actual realizers and costs.
- **B / telescoping already assumed:** [packet j report, lines 468–506](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26j/report.tex#L468-L506).
- **B / local reset and explicit scan construction already assumed:** [packet zo report, lines 440–572](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zo/report/report.tex#L440-L572). Lines 555–572 specifically advertise a seed-zero explicit constructor and its import constraint.
- **B / exact prior retained-bound statement:** [packet zn report, lines 263–274](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zn/report.tex#L263-L274).
- **B / newest translation boundary:** [packet zp report, lines 345–354](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zp/report.tex#L345-L354).
- **B / newest controller reuse boundary:** [packet zq late scope addendum, lines 89–105](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zq/evidence/late_head_scope_addendum.md#L89-L105).

Novelty is a bounded corpus judgment, not a claim of novelty in mathematics or proof engineering generally.
