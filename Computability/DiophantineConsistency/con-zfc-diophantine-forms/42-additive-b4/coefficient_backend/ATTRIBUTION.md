# Attribution and source pins

Research and code in this package were prepared with AI assistance for
Vladimir Reshetnikov's ProveIt research program on 23 October 2026.
New contributions are the nonzero-code occupancy lemma, its explicit
Wang943 instantiation, the shorter anchor/support geometry, the resulting
materialized four-port tuple and its independent audit. The universal
compiler, Pell, K215/refutation and marked tiling theorems are inherited.

All source references below are pinned to
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08` of
https://github.com/VladimirReshetnikov/ProveIt . The common path prefix is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/36-small-tuple/coefficients/`.

| Delivered item | Source item | Git blob SHA |
|---|---|---|
| `build_coefficients.py` (modified derivative) | `build_coefficients.py` | `1518d68fdd27d94c7a7b2a6623980775b4a21050` |
| `k215_transitions.json` | same name | `4f6e42b6a22cb6d961ea814a05eb3a1394a40105` |
| `wang943_tiles.json` | same name | `a57902a6862352727fd925be406fa76371dd7edb` |
| `source_proofs/package36_PROOF.md` | `PROOF.md` | `cd766747a2d3685800842776c3ad7437e4983837` |

The source proof files `WANG943_COEFFICIENTS.md`,
`WANG943_COMPACT_LAYOUT.md`, `BLANK_HELICAL_PROOF.md` and
`COEFFICIENT_TRANSFER.md` are copied from `source_proofs/` beneath the
same prefix. All supplied licence and notice files are retained in
`licenses/`. They preserve the original machine authorship and derivation
notices. The new auditor was written independently and does not import
the modified builder.

The direct antecedent credits package 25 for mixed-radix clauses,
package 24 for the prime-padding controller, and package 27 for the full
signed-interface transfer, together with their earlier sources. Those
attributions remain in the copied proof files. The source table and
language are unchanged; no claim of new machine construction is made.

## Arithmetic proofs for the concrete bound equations

The two additional inherited arithmetic proofs are copied from package 36's
`proofs/` directory, outside the `coefficients/` prefix above. At the same
reviewed commit, their complete repository paths are:

* `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_P67_PROOF.md`,
  Git blob `68cc1f7cf673cd4e8b79cdbea7795c33d57a1f6b`;
* `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md`,
  Git blob `f7ae1673df26776071b9e030018f58aa2927e83c`.

They are delivered under `proofs/` with their original names and mathematical
contents. Text materialization added one terminal line-feed to these copies,
as it did to the machine JSON, tile JSON and copied package-36 proof. The
upstream Git blob hashes above identify the original source bytes; the
delivered-file SHA-256 hashes are separately recorded in `FILE_MANIFEST.json`.
No expression, action, label, proof sentence or mathematical claim changed.
The original baseline circuit graphs are in `equations/upstream/`; each
new bound circuit records its exact source path, commit and digest in its
`provenance` field. Their arithmetic expressions, witness domains and
comparisons are unchanged. The new contribution to these two instances is
the coherent substitution of the four new fixed coefficients, justified by
the complete native-interface proof in this package.
