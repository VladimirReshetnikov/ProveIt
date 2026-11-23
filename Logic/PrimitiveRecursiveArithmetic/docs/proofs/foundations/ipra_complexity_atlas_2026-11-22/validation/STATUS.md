# Validation and formalization status

## What has been checked

All five finite check programs completed successfully under Python 3.12.14.
The ordered run and complete per-program results are in `aggregate.json`;
the individual JSON files and logs retain the detailed cases.

| Check family | Selected coverage |
|---|---|
| Numerical machine model | 675 rule-code round trips, 100 machine-code round trips, 181 distinct tables, 67,875 packed/sparse configuration comparisons, 5,103 work-tape writes, and 238 configuration-clock/cycle comparisons |
| Reductions and algorithms | 1,104 small circuits with unique extensions, 4,416 dual-rail Horn instances, 236 CNF graph/integer instances, 618 subset-sum witness bijections, 1,326 2SAT instances, and 4,096 Horn instances |
| Graph optimization | All 1,100 undirected graphs through five vertices for the vertex-cover approximation, and 6,505 parameterized cases |
| Space and QBF | 530 directed graphs, 111,108 forced-enumeration subset checks, 4,674 layered endpoint checks, and 273 actual quantified-formula evaluations |
| Randomness and lower bounds | Thirteen exact arithmetic/counting checks, documented in the log |
| Quantum paths | 8,050 small-circuit/initial-state checks against an independent rational-pair amplitude model, including zero to five Hadamard gates, plus explicit PP-branch and classical-embedding checks |

These finite checks are independent implementation checks. They are not
universal proofs, object-language iPRA certificates, or asymptotic time/space
certificates. In particular, a Python graph bitmap is not the asserted
logarithmic-workspace machine, and an array evaluator is not Savitch's stack
implementation.

## Document checks

The final PDF has 63 pages. Three pdfLaTeX passes resolve its cross-references
and bibliography. The final pass has no undefined references, rerun requests,
overfull boxes, or LaTeX warnings/errors. All fonts are embedded, and no text
span lies outside a page. All pages were rendered and reviewed in contact
sheets; six representative pages were also inspected at readable size,
including equations, proofs, and the formalization table. See
`pdf_preflight.json`, `pdf_fonts.txt`, and `report_build.log`.

The source audit found 86 unique theorem/lemma/corollary IDs, 59 topic-map
entries, no duplicate LaTeX labels, and no unresolved theorem references or
citations. See `source_integrity.json`.

## What remains unverified

No Lean executable was available, and no new Lean module was compiled.
The `lean/` directory contains uncompiled semantic definitions, proof
targets, and completion notes. No new completed kernel-checked
object-language derivation of a main complexity theorem is supplied.

The human-readable proofs give the constructive mathematical arguments.
The roadmap specifies how to turn them into finite `PR` syntax, bounded
formula syntax, derivations using quantifier-free induction, and verified
resource-machine simulations. Existing ProveIt source endpoints were
inspected at the pinned revision; their builds were not rerun.

## Reproduction

Run `python3 code/verify_all.py` from the package root for the finite checks.
Run `bash build_report.sh` with a configured TeX Live installation to rebuild
the PDF. The command `cd lean && lake build` is a prospective first step for
checking the outline with the pinned toolchain, not a command reported as
successful here.

The archive's `SHA256SUMS` records every other delivered file. Hashes check
file integrity, not proof correctness.

