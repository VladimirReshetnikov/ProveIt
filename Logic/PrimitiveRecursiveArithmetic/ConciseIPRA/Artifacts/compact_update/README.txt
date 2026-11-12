A SMALLER CHECKED PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

START HERE

  ipra_compact_update.pdf      Main report: exact result, rules, proofs, limits.
  ipra_compact_update.tex      Complete self-contained source of that report.
  code/checker_bytes.py        Complete 521-byte compact checker.
  code/checker_ast.py          Complete 278-AST-node compact checker.
  code/checker_strict.py       Complete 1201-byte public-goal validator/checker.

WHAT WAS ACHIEVED

The incoming guarded_source package already has a 522-byte checker and a
separate 279-node AST checker. Applying the scalar neutral-resource encoding
already established in the incoming reversal_core package gives 521 bytes
and 278 AST nodes, respectively. The 257-token incoming leader is unchanged.

This is an implementation-level composition of existing results. It is NOT
a new mathematical axiomatization, a significant arithmetic breakthrough,
or a proof of absolute minimality. The requested stronger mathematical
simplification was not obtained. The report states this limitation plainly.

The underlying public theory is exactly the inherited guarded-source
presentation, with its written whole-domain, actual-equality
bi-interpretation with full first-order iPRA. Its unrestricted auxiliary
proof language must not be mistaken for the public theory. The new neutral
encoding changes neither public formulas nor mathematical inference rules.

The main report also proves an exact criterion for agreement of conditional
and progressive equation closures, with counterexamples and qualifications
for existential witnesses. No literature-wide novelty claim is made for
that elementary metatheorem.

VALIDATION

  python3 reproduce.py
  python3 closure_criterion.py

The first command reproduces 258 complete-process expectations under normal
Python and Python -O, remeasures all six comparison/candidate modules, and
checks the scope of the certificate conversion. The second performs 8190
finite Boolean-sequence checks supplementing the written closure proof.
The recorded run has no failures or timeouts. These checks do not constitute
a universal soundness proof or a new Lean/Rocq verification.

One accepted canonical example:

  python3 code/checker_bytes.py < tests/zero/guarded_induction_with_used_hypothesis_local.json

The compact programs use the inherited canonical-public-statement contract.
They do not validate that every proposed goal belongs to that public grammar.
The strict program checks the canonical public goal; it does not impose an
exact integer/list type restriction on every unused certificate value.
Acceptance is exit code zero with exactly ACCEPT followed by a newline.
An exception, resource exhaustion, or other output is not acceptance.

Only the complete selected code/checker_*.py module is trusted for checking
its certificates. No checker imports the converter, tests, metrics, proof
producer, or an external axiom/theorem database. Gzip-9 figures are
informational and were not optimized.

To convert a packet produced by the frozen local producer:

  python3 convert.py < tests/old/computation_zero_local.json

The converter replaces [] by 0 ONLY in the major-premise field of a
four-field instruction. It preserves numerical terms, formulas, templates,
witnesses, and introduction-mode fields. It is not a general arbitrary-JSON
equivalence transformation. Older []-neutral certificates need conversion.

PDF BUILD

  pdflatex -interaction=nonstopmode -halt-on-error ipra_compact_update.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_compact_update.tex

The main report requires only ordinary TeX Live packages and no network,
shell escape, external figures, bibliography processor, or input files.
The inherited reference report can also be rebuilt by running the analogous
two commands on guarded_source_report.tex from within reference/.

CONTENTS AND PROVENANCE

  code/          Three complete new checker profiles and normalized gzip files.
  tests/         Frozen old packets and explicitly converted new packets.
  evidence/      Exact metrics, process receipts, provenance, claim ledger.
  reference/     Pinned README, exact predecessor checkers, inherited full
                 mathematical report/source, reversal source and Lean excerpts.
  convert.py     Untrusted narrow certificate conversion and its audit.
  reproduce.py   Measurement and complete-process test harness.

The source snapshot is ProveIt commit
a4e5e96c456303cf231eab2aeeb3291d8889833f, under
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.
The incoming archives themselves document the older comparison snapshot
1517d9d79ce33f631e0f82960c849427cbba23bf. These dates are distinguished.

All inherited material is credited in the report and distributed under the
included ProveIt MIT-0 license. The existing Lean development was inspected,
not rebuilt. The excerpt files are not a standalone Lake project. No remote
repository changes were made. SHA256SUMS covers the delivered payload before
reproduction rewrites generated receipts or PDF metadata.
