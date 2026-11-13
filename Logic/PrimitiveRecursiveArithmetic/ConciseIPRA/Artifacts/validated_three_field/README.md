# iPRA with three-field certificates

Prepared for Vladimir Reshetnikov, 13 November 2026.

## Result and limitation

This package improves the **fully validated** presentation of the inherited native scalar iPRA theory. Its separate token, AST-node, and normalized-byte records decrease from **317 / 356 / 597** to **306 / 348 / 595**. One complete checker has **313 tokens and 353 AST nodes**, improving both corresponding old minima at once.

It does **not** produce a new mathematical axiom basis or beat the permissive compact **239 / 256 / 461** envelope. The unqualified request for a presentation below all existing records therefore remains unsolved. A finite corpus minimum is not a mathematical complexity lower bound.

The ordinary realization retains the established whole-domain bi-interpretation with full first-order intuitionistic primitive recursive arithmetic: actual equality and identity graphs for the composites. These mathematical results are inherited from ProveIt; the new work is the certificate/checker implementation, its written correctness arguments, independent review, and executable validation.

## Complete checker profiles

| File | Tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| `code/checker_tokens306.py` | 306 | 362 | 668 |
| `code/checker_joint.py` | 313 | 353 | 701 |
| `code/checker_ast348.py` | 330 | 348 | 681 |
| `code/checker_bytes595.py` | 329 | 372 | 595 |

No single program attains the three componentwise minima. All four read one whole JSON input, validate the public Eq/D goal grammar, check the complete parsed input to contain only exact integers and lists, and print `ACCEPT` after a successful proof check. The profiles have different packet formats. See the report for scope, sorted encodings and exact proof obligations.

- The first two use the new three-field protocol.
- The AST profile accepts the same certificates as its four-field control, ignoring physical resource limits.
- The byte profile preserves the represented theorem language; its additional normalized terminal scan can change which noncanonical certificates succeed.
- `code/readable_three_field_strict.py` is an explanatory reference implementation, not a size contender.

## Contents

- `report.tex` and `report.pdf`: full report, all primitive inference schemes, bi-interpretation explanation, correctness proofs, comparisons, and further research questions.
- `code/`: complete checkers and readable reference.
- `controls/`: unchanged attributed incoming strict controls and compact controls for context.
- `tools/`: measurement, canonical certificate conversion, and reproduction entry points.
- `fixtures/`: positive and adversarial inputs for the separate protocols.
- `notes/`: detailed mathematical and independent review notes.
- `evidence/`: source provenance, measurements, test receipts, and static corpus comparison.
- `reference/`: original base-theory and checker chapters, plus the upstream license. These two chapter sources are documentary parts of the original article; compile `report.tex` for the standalone report.
- `STATUS.json`: precise machine-readable claim boundaries.
- `MANIFEST.sha256`: hashes of the other final files.

## Reproduce

Use **CPython 3.12.14** for exact source-measurement reproduction:

```sh
python3 tools/measure.py --check
python3 tools/verify.py
python3 code/checker_joint.py < fixtures/example_three_field.json
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The final executable reproduction comprises **710 isolated executions with zero failures**: 320 family-control comparisons and 390 runs of the two three-field checkers and their readable reference. Both ordinary and `-O` Python runs are covered. The three test suites have 37, 43 and 65 protocol-specific cases.

The static audit compares the four new checkers against 3,247 parseable upstream/incoming Python sources (1,759 distinct normalized ASTs) and finds no exact duplicate. This does not prove novelty of the mathematical devices, which are credited in the report.

The correctness claims are written arguments reviewed independently. The finite tests are supporting evidence. No new end-to-end Lean or Rocq verification of the Python code is claimed. Source size does not measure proof length, runtime, or absolute mathematical simplicity.

## Provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `798856e4ef2d02b7f9c0f1660828c5ce58f277f2`

Subproject: `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`

All five incoming archives at that revision were inspected. Exact archive Git-blob hashes match the pinned tree; the receipt records SHA-256 hashes as well. Upstream material is distributed under the MIT No Attribution license in `reference/PROVEIT_LICENSE.txt`.
