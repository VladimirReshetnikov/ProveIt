# Source provenance and scope of inspection

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `4e128356d0ef75308be8ed405d89aea2ffdb8a57`

Commit timestamp returned by GitHub: 2026-09-30T18:47:30Z.
Inspection date: 30 September 2026.

The GitHub connection was used to read the branch and the selected files.
The branch's future movement does not change the sources cited below.

### Selected files used substantively

1. Hilbert's tenth problem README:
   https://github.com/VladimirReshetnikov/ProveIt/blob/4e128356d0ef75308be8ed405d89aea2ffdb8a57/Computability/HilbertTenthProblem/README.md

   Establishes the repository's stated MRDP interface, Jones formalization,
   and updated 75-operation complete-certificate baseline. These status
   claims were read, not independently rebuilt or kernel-audited here.

2. Arithmetic machines / FRACTRAN alternatives note:
   https://github.com/VladimirReshetnikov/ProveIt/blob/4e128356d0ef75308be8ed405d89aea2ffdb8a57/Computability/HilbertTenthProblem/Papers/1980/FRACTRAN_VARIANTS.md

   Identifies priority, terminality, input conversion, and history validity
   as genuine obligations. Its 90-operation historical baseline must not
   be confused with the newer README's 75-operation result.

3. Vendored Coq FRACTRAN Diophantine development:
   https://github.com/VladimirReshetnikov/ProveIt/blob/4e128356d0ef75308be8ed405d89aea2ffdb8a57/lib/Coq-Library-Undecidability/theories/H10/Fractran/fractran_dio.v

   Inspected declarations include `dio_rel_fractran_step`,
   `dio_rel_fractran_rt`, `dio_rel_fractran_stop`,
   `dio_rel_fractran_eval`, `FRACTRAN_HALTING_on_diophantine`,
   `FRACTRAN_HALTING_on_exp_diophantine`, and
   `FRACTRAN_HALTING_dio_single`. In the last identifier, "single"
   concerns an equation, not automatically unique auxiliary witnesses.
   The file attributes original code to Dominique Larchey-Wendling and
   identifies its MPL-2.0 license. That code is not redistributed here.

The root README was also read for navigation. Unrelated claims in it are
not dependencies of this article. This was not a full repository audit,
a complete search for every related manuscript, or a Lean/Rocq build.

## External literature

Primary works checked for semantics and the established background:

- J. H. Conway, *FRACTRAN: A Simple Universal Programming Language for
  Arithmetic*, 1987, pp. 4–26:
  https://gwern.net/doc/cs/computable/1987-conway.pdf
- D. Larchey-Wendling and Y. Forster, *Hilbert's Tenth Problem in Coq
  (Extended Version)*, LMCS 18(1), article 35 (2022):
  https://arxiv.org/abs/2003.04604
  DOI: 10.46298/LMCS-18(1:35)2022.
- C. Barrett, S. Demri, M. Deters, *Witness Runs for Counter Machines!*,
  FroCoS 2013, LNAI 8152, pp. 120–150:
  https://theory.stanford.edu/~barrett/pubs/BDD13.pdf
- N. Decker, A. Pirogov, *Flat Model Checking for Counting LTL Using
  Quantifier-Free Presburger Arithmetic*, 2019:
  https://arxiv.org/abs/1901.05692

Historical/contextual reference, not a dependency of the new proofs:

- D. Cantone, L. Cuzziol, E. G. Omodeo, *A Brief History of Singlefold
  Diophantine Definitions*, CILC 2023, CEUR 3428:
  https://ceur-ws.org/Vol-3428/paper5.pdf

## Contribution boundary

The sharp capacity formula and threshold, the fully specified canonical
quartic compiler with exact size accounting, and the other stated results
are proved in the accompanying manuscript. No external source is cited as
proving those exact formulations. Conversely, finding no exact match in a
limited search would not establish novelty: literature-wide priority is
expressly unverified. Fixed-loop acceleration, arithmetic circuit
quarticization, invariant checking, FRACTRAN universality, and MRDP are
established background, not claimed discoveries.

The manuscript does not assert that a named longstanding open conjecture
has been resolved. Its further research questions are locally proposed
questions, not a claim that each has already been recognized as open in
the literature.
