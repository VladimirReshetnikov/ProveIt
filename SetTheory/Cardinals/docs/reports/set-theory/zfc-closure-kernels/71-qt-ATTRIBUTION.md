# Attribution and inherited material

This contribution was prepared for Vladimir Reshetnikov's ProveIt repository on 18 October 2026. The 244-state table is a three-row modification and one-state deletion of the supplied routing245 construction. It retains the underlying numerical calculus, proof enumerator, arithmetic engine, initial logical state, and consistency calibration.

The supplied repository credits Mira-Cult for the compact source calculus and original construction, Jeff Ketchersid for verification, and Andrew James Wade for the compiler framework. ProveIt's contributors supplied the preceding permutation, prefix, grammar, routing, bootstrap, and proof developments. Those attributions apply to the substantial inherited material here.

The exact new contribution is the concrete transfer-plus-one loop rotation in this source and its binary decoder, the resulting 244-state table, the independent universal source proof and frame/blank/literal checks, the complete changed-table runtime replay, and the accompanying alternative-formalism research. Loop rotation and the classical Tarski–Bernays propositional basis are established ideas; no claim is made to invent either general idea.

## Preserved inputs

- `reference/baseline245/` is the unmodified portable 245-state proof package, except that transient Python bytecode is not copied. Its original `SHA256SUMS` remains valid for all 293 listed files, and its original notices and licenses remain in place.
- `research/formalisms/formalism_reference/PROVENANCE.json` identifies the symbolic emitter, fine dictionary, original program, set-theory specification, and Wade backend used by the alternative source experiments.
- `research/grammar/reference/` preserves the relevant ProveIt and Wade licenses and notices. Its portable wrappers retain the original source and grammar data.
- `research/joint-source/reference/` contains attributed formula-source and DNE material from the inspected incoming research packages. The parent `PROVENANCE.json` lists the exact incoming archive hashes.

The root frame checker is adapted from the baseline's `code/verify_machine_frame245.py`; its new table counts, source counts, bootstrap, and exact hash assertions are documented in `PROVENANCE.json`. The runtime wrapper uses the baseline's unchanged block/list induction and symbolic-execution implementations against the actual new table. The independent source rotation, blank interpreters, and finite literal checker do not import those proof engines.

Existing licenses and notices govern the inherited material. This file does not replace or override any of them. Mathematical statements and new explanatory text should remain associated with their exact machine, source, and proof-scope qualifications when incorporated into the repository.
