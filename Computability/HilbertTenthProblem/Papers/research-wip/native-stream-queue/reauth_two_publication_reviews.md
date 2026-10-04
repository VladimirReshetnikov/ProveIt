# Independent reauthentication of two frozen publication reviews

PASS. A wholly new read-only checker reproduced the immutable byte and structural
records of both frozen scoped reviews. It did not execute or import either
review's collector, any supplied/archive program, or any predecessor helper.
No repository file or Git state was changed.

| Input | Frozen receipt SHA-256 | Frozen review SHA-256 |
|---|---|---|
| `review_polish_borel_9a8894d0a` | `8369c3fe61d9dcbaff643beb32b76abacfdf0bba17548a5bc66e600bd91e2e16` | `2643f8ae2df4c0e2f00b175f69f73d0cdeb645b3d1feb600b95d7b61fac03900` |
| `review_definable_publication_c7d65e30b` | `47e29c2276d241a8dd7cc14b5ee2a0e53e0ac6e8f3881cadd3db3108143ab7a7` | `5c636dbaf2bf11dd17dd14b6147de4a9c2529affab2d360257108cca0f51e8e1` |

The publication commits and their exact parents were independently resolved.
Each changed-path set equals the three files declared in its receipt. All
before/after file records, contextual Git records, ZIP records and placement
records were checked against their recorded commit/path, blob ID, byte length
and SHA-256. The two old collectors were hashed as inert bytes solely to verify
their receipt provenance.

| Achieved check | Polish | Definable |
|---|---:|---:|
| Git file records authenticated (records, not distinct objects) | 23 | 24 |
| Full diff hashes reproduced | 2 | 3 |
| Hashed source/diff/archive read spans authenticated | 16 | 26 |
| ZIP archives / complete regular-member inventories | 2 / 17 | 3 / 17 |
| Exact member-to-placement comparisons | 9 | 7 |
| Source-label routes checked | 126 | 198 |
| Before / after unique label counts | 1,156 / 1,344 | 139 / 346 |
| Literal internal references / distinct referenced labels | 3,793 / 981 | 820 / 249 |

All old labels retain their relative order; both after-articles have no duplicate
labels and no unresolved literal internal references in the parser's scope.
The definable review additionally reproduces all 202 recorded target-line hashes
and verifies that each recorded label occurs on that line. A new source-syntax
counter scanner reproduces all 80 source/publication statement-number pairs,
including the recorded changes from theorem/corollary to remark. Its seven-entry
delivered SHA256SUMS file agrees with the actual ZIP members and the receipt.
The Polish ancillary files are also unchanged from the publication's parent;
the definable files agree at both their original placement and publication.

All 1,175 recorded check events passed. The fresh checker was run normally and
with `python -O`, both from `/`; the resulting receipt bytes were identical.
It uses explicit exceptions rather than relying on Python assertions.

This verifies the bytes identified by a declared read span, not that the span
was read or that its mathematics was proved. It adds no mathematical review,
full manuscript-body equivalence, external-paper audit, priority claim, PDF
rendering or build validation. Editorial correspondence routes authenticate
their target lines; they do not establish semantic equivalence. The reference
and statement-number checks are literal source analyses, not a general TeX
macro evaluator. Current working edits are outside the immutable snapshots.

Exact proposed Polish README replacement blocks are saved separately in
`/tmp/polish_borel_9a8894d0a_replacements.txt`, SHA-256
`e011139e0e62272a4e89b417ada74f552bd403f00b22b488f242d44cbb8d49fd`.
Each OLD block was verified to occur exactly once in the immutable README.
The file preserves numbered remarks R1–R3 and the zero-derivation, zero-ordinal,
zero-space and atomic-measure counterexamples. No proposed replacement was
applied to repository files by this task.

Frozen new artifacts:

- `/tmp/reauth_two_publication_reviews.py`:
  `729c2211340200bf7fb75c9a2c8442d8b07a7dac5e9a3c0cb0c474ee95a6ce95`.
- `/tmp/reauth_two_publication_reviews.json`:
  `e9bb26980476cba35029c0f17530126e7c1b34330b1d45d7a230ef975b4d654d`.

The checker is scoped to the two pinned `/tmp` review pairs and immutable Git
objects; it does not depend on importing their collectors.
