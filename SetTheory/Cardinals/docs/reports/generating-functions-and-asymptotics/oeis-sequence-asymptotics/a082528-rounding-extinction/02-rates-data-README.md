# Bounded OEIS integer fixtures

`oeis_fixtures.json` contains exactly 342 integer terms from the displayed
sequence sections of four records in The Online Encyclopedia of Integer
Sequences (OEIS):

- [A002491](https://oeis.org/A002491): 53 terms, indices 1–53, threshold `B_1(k)`;
  record revision 109, dated 2026-08-20; credited to N. J. A. Sloane
- [A073047](https://oeis.org/A073047): 79 terms, indices 1–79, stopping index
  `A_1(n)`; revision 15, dated 2020-06-07; credited to Benoit Cloitre
- [A082527](https://oeis.org/A082527): 105 terms, indices 0–104, stopping index
  `A_2(n)`; revision 8, dated 2025-12-11; credited to Benoit Cloitre
- [A082528](https://oeis.org/A082528): 105 terms, indices 0–104, stopping index
  `A_3(n)`; revision 6, dated 2012-03-30; credited to Benoit Cloitre

The integers were extracted from official `oeis/oeisdata` records inspected on
2026-10-03. The fixture records give source links, revision metadata, and SHA-256
hashes of the complete source records used for extraction; those records are not
included. The fixtures reorganize only the integer terms and minimal provenance.
No prose comments, third-party programs, b-files, or raw record exports are
redistributed. Live records may change after these fixed revisions.

Attribution: The Online Encyclopedia of Integer Sequences,
[The OEIS Foundation Inc.](https://oeis.org/), and the credited individual
contributors. These fixtures are redistributed under
[Creative Commons Attribution-ShareAlike 4.0 International](https://creativecommons.org/licenses/by-sa/4.0/),
as stated in the [OEIS license](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement).
The transformation was extraction into bounded JSON integer fixtures with added
provenance and index conventions. This attribution and license apply to the
OEIS-derived fixtures; the Python code is original.

All 342 fixture integers are checked by `../code/check_exact.py`. The checker
also enforces the four sequence identities, offsets, counts, and kinds, so an
accidental omission or first-zero/last-positive offset change fails explicitly.
