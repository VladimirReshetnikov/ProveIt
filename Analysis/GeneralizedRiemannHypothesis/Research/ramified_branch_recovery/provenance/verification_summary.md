# Verification summary

Prepared 26 November 2026, America/Los_Angeles.

## Mathematical proof

The paper supplies proofs of the exact observation kernel, unresolved-jet
dimension, relative block distance, error/erasure criterion, adversarial
capacity recurrence, saturation formula, Lubin–Tate specialization, and
sharp binary example. The finite example also has a small hand-checkable
capacity certificate, so its upper bound does not depend on trusting an
exhaustive program.

A separate internal reviewer examined the valuation/Newton argument,
elementary formal-series division, filtration noncancellation, threshold
strictness, empty/singleton cases, hand certificate, saturation argument,
and scaled family. The final text incorporates the resulting corrections.
This is internal mathematical review, not external peer review.

## Main exact computation

`code/verify.py` completed successfully. Its recorded output is
`results/verification.json`. All mathematical computation uses integers and
exact finite-field arithmetic, not floating-point approximations.

| Check | Coverage or result |
| --- | --- |
| Direct greedy spectra vs tree merge | All 256 subsets of eight branches |
| Capacity recurrence vs exhaustive subsets | 240 states, with backtracked witnesses |
| Worst ten-branch configuration | All 8,008 subsets; maximum sixth factorial 14 |
| Number of maximizing ten-branch subsets | 16 |
| Direct substitution matrices | 13 cases, including the immediate failure/success boundary |
| Explicit precision-14 ambiguity | Six nonzero blocks, received data within three errors of both explanations |
| Reference decoder at precision 15 | All 560 candidate three-error location sets inspected; target recovered |
| Decoder guard | Rejects a case with unresolved target freedom |
| Saturation | Precision 21, distance 11 |

The separate CSV contains every integer precision from zero through 27.
The pure-error cutoffs for error budgets 0,1,2,3,4,5 are respectively
10,10,11,15,19,21.

## Independent programs

These programs do not import `branch_recovery.py`.

| Program | Recorded check |
| --- | --- |
| `independent_jet_check.py` | 4 fixed and 75 deterministic random direct-substitution checks over F2, F3, F5; 62 tie-independence checks |
| `independent_tree_check.py` | 30 deterministic random configurations, 1,881 capacity states, 1,162 enumerated subsets |
| `independent_nonpacking_check.py` | Separate enumeration of all 8,008 ten-branch sets and direct polynomial evaluation of the ambiguity witness |

Their exact outputs are the correspondingly named JSON files in `results/`.
The seeds are fixed in the source. Successful completion of the assertions
certifies these finite comparisons, not the general mathematical theorems.

## PDF and archive

The final LaTeX source was compiled twice with pdfTeX. The 14-page PDF has
embedded scalable fonts, resolved citations and cross-references, and no
overfull boxes. All pages were rasterized for visual inspection; the two
figures are also supplied separately as vector PDFs and PNGs. The archive
contains no transient TeX build products or Python bytecode.

## Boundaries

No upstream Lean build or exported-proof replay was run in this project.
No formal Lean proof of the new theorem was compiled. External upstream
verification is attributed to the primary records in `source_audit.md`.

The new proofs apply to distinct formal branches over a field and to
uniform truncation precision. The Lubin–Tate specialization is over the
residue field. Higher coefficient precision and unequal truncations are
not claimed. The capacity dynamic program is pseudopolynomial in numeric
precision. The reference decoder enumerates candidate error locations;
no fast general error-location algorithm is claimed.
