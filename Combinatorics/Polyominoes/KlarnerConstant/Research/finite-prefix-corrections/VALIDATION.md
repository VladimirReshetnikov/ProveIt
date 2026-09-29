# Validation record

## Mathematical and computational boundary

The proofs in the article are written mathematical arguments. No new theorem
in this package has been checked by Lean or another proof assistant. The new
polyomino bound imports the geometric recurrence lemma and depends on the
correctness of the exhaustive marked enumeration described in the article.

## Exact arithmetic

The final `python3 code/verify.py --report data/verification.json` run passed
all structural checks, table-consistency checks, twelve upper certificates,
the integer monomial-balance equations and rational logarithm enclosure, and
the old repository certificate. The transcript is `data/verification.txt`.
Numerical critical points and eigenvectors play no role in these decisions.

## Enumeration checks

The archived CSV and JSON agree in all 18 unmarked and 306 marked entries.
The independent Python set-expansion output agrees with all 11 unmarked and
187 marked entries through size 11. The direct-scanning C++ enumeration
agrees through size 16 with the incremental enumeration.

After preparing the deliverable, the final incremental C++ source was
compiled afresh and run through size 16, reproducing all corresponding
entries. The final direct-scanning source was compiled with address and
undefined-behavior sanitizers and run through size 11; it reported no
sanitizer error and reproduced that prefix.

The final command-line changes only add size-argument validation; the
size-18 mathematical generator and pattern masks are unchanged from the
full enumeration used for the main table. A fresh size-18 rerun was not
performed after those command-line changes. Both programs explicitly limit
sizes to 18, the range covered by the article's storage and overflow bounds.

These cross-checks do not constitute a formal certificate that every
size-18 object was generated exactly once. That statement relies on the
algorithm and correctness proof, and remains a priority for independent
verification and formalization.

## Document build

The final article compiled with `latexmk`/pdfLaTeX to 27 pages, with no
undefined references, overfull-box warnings, or duplicate PDF destinations.
All pages were rendered; the layout was reviewed with contact sheets and
full-size inspections of the principal tables. The PDF contains the title
page, one-page contents, full proofs, numerical and exact-certificate tables,
all marked counts through 18, a minimal checker, a claim/source audit, and
bibliography.
