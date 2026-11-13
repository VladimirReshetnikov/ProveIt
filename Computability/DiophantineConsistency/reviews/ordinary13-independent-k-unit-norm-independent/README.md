# Independent review of the independent-k literal and unit draft

The reviewed packet is `research/ordinary13-independent-k-unit-norm-draft/`. The independent checker reads the candidate JSON and directly parses the Lean literal, without relying on the literal generator, then compares all 84 ordered operation rows, all 13 witness slots, four port indices, and every exported structure field. It confirms that slot 9 is eta, slot 10 is the independent `n_k`, and there is no eta-plus-zeta operation. The generated literal's tuple maps its first and main residuals, auxiliary and strong factors, output, and root fields to the intended rows.

The source bridge is the exact stated parent adaptation with the imported graph and namespaces changed; this review does not treat the parent as a proof of the child without re-elaboration. The `factor_units` statement assumes an actual `InternalZero` of the child output. Its proposed proof uses the signed-pair product-of-units lemma and excludes the negative unit for each factor; the subsequent `residuals_zero` and `signed_norms` have the expected directions and use the child's independent k field. The inspected generic `FreeJ13` definitions and signatures match the main, auxiliary and strong pattern calls, and the inspected signed-pair sources contain the cited magnitude and residue interfaces. All ports are arbitrary integers in these statements; positivity, compact masks and an eta/k relation are not tacit premises of the proposed factor argument.

As an additional arithmetic control, the checker independently exhausts all residue classes modulo 4 for each of the four patterns: 4^5 cases for the first, 4^4 each for the main and auxiliary, and 4^3 for the strong. This verifies the finite residue statements as ordinary arithmetic, not Lean elaboration or arbitrary-model soundness. The source `rfl` pattern equalities, model instances, transitive dependencies and axiom sets remain unverified until a coherent Lean build. No full parent-child zero correspondence or iPRA endpoint follows from this review.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-unit-norm-independent/check.py | cmp - reviews/ordinary13-independent-k-unit-norm-independent/receipt.json
```

The checker also replays the author's source-only receipt. It is not a Lean parser or type checker; no Lean, build, staging or provider replay was performed.
