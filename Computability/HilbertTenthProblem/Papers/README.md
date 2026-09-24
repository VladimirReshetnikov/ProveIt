# Corrected editions of six articles on Diophantine representation

This directory holds the continuously revised corrected editions of six
articles by J. P. Jones and coauthors (1974–1984), their editorial notes and
their verification programs. The editorial notes compare each edition with
the journal scan and its raw Mathpix OCR, which they cite as
`original/<year>/jones<year>.pdf` and `original/<year>/jones<year>.tex`;
these inputs are not included here. The editions are modified in place as
further corrections are found; `EDITORIAL_NOTES.md` is their dated log.

## Layout

| Path | Contents |
|---|---|
| `<year>/jones<year>_corrected.tex`, `.pdf` | The corrected edition and its PDF (engines: pdfLaTeX; LuaLaTeX for 1978; XeLaTeX for 1982). The original journal pagination is marked in the margin (`\origpage{n}`, line accuracy, checked against the scans). |
| `<year>/jones<year>_editorial_notes.md` | The editorial notes for one article: every discrepancy between the naive Mathpix OCR of the scan and the edition, with its classification and justification; editorial additions; readings examined and retained; verification summary. **Start here** for one article. |
| `EDITORIAL_NOTES.md` | The dated log of revisions and checks: each change with its location in the original pagination, old and new text, classification and reason; checks that found nothing; findings fed back from the Lean formalization in `../Lean/`; the operation-count work on the 1980 Theorem 5; environment notes. |
| `verification/round4_<year>_checks.py` | Independent per-article checks; each writes `round4_<year>_results.json` next to itself. Run with `PYTHONUTF8=1 python verification/round4_<year>_checks.py`. |
| `verification/jones<year>_*`, `corpus_*` | Further per-article and cross-article checks, reading the current sources: `jones1974_verify_machines.py`, `jones1974_verify_counts.cpp`, `jones1976_verify_mathematics.py`, `jones1976_verify_87_operations.py` (which writes the 87-operation certificate `jones1976_primality87.json` and `.md`), `jones1978_validation.py`, `jones1982_verification.py`, `jones1984_verification.py`, `corpus_cross_review.py` and `corpus_review.py`. Each writes its results next to itself. |
| `verification/round4_1976_theorem39.wl` | Wolfram Language instantiation of Theorem 3.9 (1976) for `k = 1`. |
| `verification/round4_1982_lemma225.py` | Numerical instances of Lemma 2.25 (1982). |
| `verification/roundNN_1980_*`, `explore_*`, `audit_*` | Operation-count reconstruction and the straight-line certificates for the 1980 Theorem 5 (see below). |
| `1980/jones1980_theorem5_operations.tex`, `.pdf` | Satellite article on the operation count `o = 100` of the 1980 Theorem 5 and on explicit straight-line certificates; the generated tables `jones1980_theorem5_*schedule*.tex` and the sectional drafts `jones1980_theorem5_optimization.tex`, `jones1980_pell_optimization.tex`, `jones1980_theorem5_short_masks.tex` are its inputs. |
| `1980/*_PROOF.md`, `1980/EXPLORATION_*.md` | Standalone proofs of the equivalences used by the successive certificate reductions, and explorations of alternatives. |

## Findings

- Every displayed system, machine table and count of the six articles was
  re-derived by the checkers. The corrections to the printed articles are
  justified entry by entry in the editorial notes.
- The Lean 4 formalization in `../Lean/` (1974, 1976 §2–§3, 1978, 1982
  §2–§5, 1984 §2–§3) found no incorrect printed statement beyond those
  corrected; the proof details it had to supply are recorded as
  clarifications in the notes.
- The 1980 operation count `o = 100` is explained (the number of indicated
  `+`, `−`, `×` signs, exponentiation not counted), and Theorem 5 is given
  explicit, symbolically verified straight-line certificates. The satellite
  article reduces the count from 129 to 89 operations; the smallest complete
  certificate established since uses **76 operations (41 multiplications and
  35 additions)**, with 30 positive existential witnesses and 19 equations
  ([`FIXED_RAW_UNIVERSAL_76_PROOF.md`](1980/FIXED_RAW_UNIVERSAL_76_PROOF.md),
  checked by `verification/explore_fixed_raw_universal_76.py`). The
  75-operation Rule 110 finite-history system still lacks a complete
  universal input and acceptance interface and is a separate component.

## Working rules

- Edit the `.tex` sources here in place.
- Record every change in `EDITORIAL_NOTES.md`, with the original pagination,
  before or with the commit that makes it, and bring the article's
  `jones<year>_editorial_notes.md` entry to the final state.
- Rebuild the PDF with the engine listed above (two passes) after any
  source change, and re-run the affected `round4_<year>_checks.py`.
- Keep the edition notice at the top of each `.tex` accurate.
