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

The [native-stream queue WIP handoff](research-wip/native-stream-queue/README.md)
preserves the conditional six/eight-operation stream component, portable
independent audits, unfinished controller research and archived scratch
evidence. Its [continuation prompt](research-wip/native-stream-queue/CONTINUATION_PROMPT.md)
records the current75-operation certificate and87-operation polynomial
frontiers alongside the historical handoff. The
[complete half-binomial75 proof](1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
supplies the comparison bound; the
[normalized strong87 proof](research-wip/native-stream-queue/complete75_normalized_strong87.md)
supplies the single-polynomial bound. The separate explicit
[coupled-unit U9/tag construction](research-wip/native-stream-queue/neary_woods_universal_joint_and_coupled.md)
now gives262 certificate / **297=144M+153A polynomial operations**,
12 comparisons,51 positive witnesses, four positive program parameters
and degree at most2311. It preserves the accepted outer relation through
sign recovery and a conditional positive restoration; the supplied
positive zero sets are not asserted identical. The
[coupled partition frontier](research-wip/native-stream-queue/neary_woods_universal_joint_and_coupled_partitions.md)
includes301=142M+159A/degree-at-most1092,302=143M+159A/756 and
304=143M+161A/608, all with51 witnesses. The304 option has257 certificate
operations and16 comparisons; the subset search is exhaustive only for
its stated factor family and propagated degree bounds. The
[two-index301 parent](research-wip/native-stream-queue/neary_woods_universal_joint_and_arithmetic.md)
remains available at260 certificate operations,14 comparisons and degree
at most2475.
The earlier [grouped finalizers](research-wip/native-stream-queue/neary_woods_universal_joint_and_partitions.md)
give alternatives303=143M+160A with degree at most1522,
305=143M+162A with degree at most1144, and308=142M+166A with degree
at most1076, all with51 witnesses. The finite search optimizes the
propagated degree bounds only within its specified partition family.
The [earlier303 source](research-wip/native-stream-queue/neary_woods_universal_joint_and_units.md)
remains reproducible at degree at most2285. Its
[raw joint-AND parent](research-wip/native-stream-queue/neary_woods_universal_joint_and.md)
gives246 certificate /356=155M+201A,37 comparisons,64 witnesses and
degree at most580. These are upper bounds including all program coordinates.

A paid lower-output bound permits one native AND to replace the separate
recoder/history AND cores. Positive native extensions are rebuilt;
the complete outer relation is preserved without a bijection of all old
and new native tuples. The two remaining cores have one checksum.
The [377/379 predecessor](research-wip/native-stream-queue/neary_woods_universal_population377.md)
remains reproducible at66 witnesses and degree bounds2285/2241.

The [population-fusion obstruction](research-wip/native-stream-queue/native_population_and_fusion_obstruction.md)
shows why simply concatenating the remaining geometry index and truth
fields fails: excess field population compensates for the wrong width
on positive recoder tuples with x=1,z=2. Their full native extensions do
not supply an accepting fixed-tag history or false universal-polynomial zero.
The [Wang B tape component](research-wip/native-stream-queue/wang_b_single_and_tape.md)
provides a complete head/read/mark scalar graph in74 certificate /124
polynomial operations,24 witnesses and degree at most40. A finite-window
initialization of literal Wang input uses two gates after a paid initial
head/read predicate. The [packed tape successor](research-wip/native-stream-queue/wang_b_packed_tape.md)
pays arbitrary-duration chronological reads and optional marks in139
certificate /192 polynomial operations,18 comparisons,31 witnesses and
degree at most232. Head motion, control and TM input coding remain open.
The [finite-game positive NOR compiler](research-wip/native-stream-queue/lattice_game_positive_nor.md)
forces exact Boolean outcomes on every fixed acyclic option graph with
one bilinear row per nonterminal. Its degree-at-most-four family grows
with the graph; no uniform lattice-game or ordinary-input bound follows.

That predecessor joins the [joint positive scale bound](research-wip/native-stream-queue/neary_woods_universal_population_joint_bound386.md),
[154-gate shared history](research-wip/native-stream-queue/neary_woods_universal_shared_history382.md)
and [padded checksum sign lemma](research-wip/native-stream-queue/neary_woods_universal_population_checksum387.md).
The [389-operation projections](research-wip/native-stream-queue/neary_woods_universal_population_projection389.md),
[395-operation bound deletion](research-wip/native-stream-queue/neary_woods_universal_population_bound395.md)
and [399-operation population parent](research-wip/native-stream-queue/neary_woods_universal_population_tag.md)
remain reproducible. The separate75/87 frontier is unchanged.
The [local target CRT theorem](research-wip/native-stream-queue/complete75_linear_strong87_target_crt.md)
realizes nearby wrong targets for a weakened auxiliary system, not full
polynomial zeros; the87-operation,degree183 candidate remains unresolved.
The [positive-index86 theorem](research-wip/native-stream-queue/complete75_weakened86_positive_index.md)
proves the unresolved86 candidate sound whenever its computed R>0,
without assuming alpha>Z. R=0 is impossible; the negative-R branch
remains unresolved, so the established75/87 bounds are unchanged.
Native queue components retain their separate scope.

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
  certificate established since uses **75 operations (41 multiplications and
  34 additions/subtractions)**, with 30 positive existential witnesses and 19 equations
  ([`FIXED_RAW_UNIVERSAL_75_PROOF.md`](1980/FIXED_RAW_UNIVERSAL_75_PROOF.md),
  checked by `verification/explore_fixed_raw_universal_75.py`). The
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
