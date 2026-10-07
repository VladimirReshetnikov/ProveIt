# Sources, attribution, and proof scope

## OEIS data

The byte-preserved numerical b-files `data/b065094.txt` and `data/b065095.txt`
were retrieved from the official OEIS on 3 October 2026:

- OEIS Foundation Inc., [A065094](https://oeis.org/A065094), floor running means,
  [b-file](https://oeis.org/A065094/b065094.txt)
- OEIS Foundation Inc., [A065095](https://oeis.org/A065095), ceiling running means,
  [b-file](https://oeis.org/A065095/b065095.txt)

Each stored b-file contains exactly indices 1 through 1000. The short complete
published prefixes in `data/oeis_prefixes.json` were extracted from the official
records retrieved the same day. Consult the linked OEIS records for individual
contributors and [OEIS license information](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement).
This archive makes no claim of authorship of OEIS sequence data. The checked
floor and ceiling constants were numerically recorded by Václav Kotěšovec in
October 2024. The stored data is reproduced for attribution, exact comparison,
and reproducibility, without copying complete third-party article texts.

The unrounded identification with `L_(n-1)(-1)` is already in
[A376995](https://oeis.org/A376995). Some ancillary text in the rounded entries
has floor/ceiling typographical inconsistencies. Computations here follow their
unambiguous defining names/formulas and integer terms, which agree exactly.

## Classical asymptotic input

Alfredo Deaño, Edmundo J. Huertas and Francisco Marcellán, *Strong and ratio
asymptotics for Laguerre polynomials revisited*,
[arXiv:1301.4266](https://arxiv.org/abs/1301.4266), especially formula (3),
Theorem 2 and equation (27). Its classical Perron expansion, with the shift from
polynomial degree n-1 to sequence index n, is the all-orders analytic input.
It attributes the classical result to Perron and Szegő. Formal recurrence
cancellation alone is not used as a proof that an asymptotic expansion exists.
The paper and its full text are not bundled.

## Authored proof and code

Report186.tex and the package's mathematical programs present the bounded-forcing
amplitude and shadowing argument, exact interval implementation, and its
consequences. The existing generic isolated build/manifest framework was adapted
to this report. The certificate retains the exact original N=10000 calculation's
published 70-place endpoint strings. A separate exact rational endpoint check
establishes 69 common truncated decimal places for all six constants. The two
printed ceiling-A endpoints share only 68 fractional digits; the others share 69. The independent positive-sum audit uses a separate computation of P and T.
Optional mpmath and SymPy scripts are diagnostics, not interval proofs.

Source data and the frozen published certificate are checked against
`data/SOURCE_DATA_HASHES.json`. Whole-release files are covered by
`SHA256SUMS.json` after building. These hashes detect changes against the supplied
receipts; they are not signatures or an authentication trust root. There is no
claim of a worldwide novelty search, proof-assistant certification, explicit
asymptotic onset, or an effective arbitrary-threshold decision procedure.
