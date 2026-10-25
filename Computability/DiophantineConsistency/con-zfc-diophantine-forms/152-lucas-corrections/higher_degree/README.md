# Direct proof equations after monic elimination

This package specifies eight complete ordinary polynomials obtained by
acyclic monic elimination from the accompanying **248-variable direct
C222 quartic**. Every unknown ranges over the unrestricted integers.
Each equation has no integer solution if and only if Con(ZFC), provably
in ZFC by composition with the retained source calibration.

| Integer variables | Degree | Residuals | Expanded coefficient height bound |
| ---: | ---: | ---: | ---: |
| 225 | 6 | 159 | < 2^27 |
| 153 | 8 | 87 | < 2^47 |
| 144 | 12 | 78 | < 2^50 |
| 125 | 16 | 59 | < 2^80 |
| 117 | 32 | 51 | < 2^144 |
| 111 | 64 | 45 | < 2^173 |
| 102 | 256 | 36 | < 2^691 |
| 94 | 65,540 | 28 | < 2^164870 |

Useful comparisons are the 153-variable octic, the 125-variable degree-16
equation, and the 102-variable degree-256 equation. The latter two remove
49.6% and 58.9% of the source coordinates. The 94-variable endpoint has a
much higher degree. These are concrete tradeoffs within the direct proof
calculus, with no claim of worldwide dimension minimality.

## Definitions and proof

`section.tex` contains the complete new monic-elimination theorem and
proof, the exact degree argument, the coefficient-height bound, and the
composition yielding the consistency equivalence. It is written as a
section for the integrating report; it expects the standard `theorem`,
`lemma` and `proof` environments and the `\Z` macro.

`pivot_appendix.tex` prints all eight complete row-to-coordinate pivot
tables and the finite substitution rule. It additionally needs the
`longtable` package. Together with the complete 248-source residual list
printed by the integrating report, these tables specify the polynomials
without executing a search or making any compiler choice.
`PIVOT_TABLES.tsv` supplies the same data in a tab-separated text format.

Each JSON in `equations/` is a complete polynomial arithmetic DAG. Its
only leaves are the declared variable inputs and literal integers; every
other node is binary addition, subtraction or multiplication. Registers
abbreviate polynomials and do not add quantified unknowns. Input order is
the increasing sequence in `retained_source_indices`. Their records in
`variables` retain the source metadata for interpretation.

`certificates/` contains the complete monic pivot selections.
`RESULTS.json` gives the certified metrics, including exact degree and
live operation counts. Each polynomial has its own top homogeneous
nonvanishing certificate. `DEPENDENCY_CERTIFICATES.json` gives exact
nonzero modular partial derivatives proving that every declared input
occurs in the collected polynomial. These finite nonvanishing proofs
are deterministic certificates, not statistical identity tests.

## Complete octic expansion

`expanded/octic_expanded.json` contains every collected coefficient of
the 153-variable degree-eight polynomial: **188,579 nonzero monomials**,
with exact coefficient height **750,273,658,864**.
`expanded/octic_residuals.json` gives its 87 substituted residuals,
containing 3,476 monomials in total.

Sparse terms have the form `[coefficient, monomial]`, where a monomial is
the sorted list of input indices with repetition. For example,
`[7,[0,0,3]]` means seven times the square of input zero times input three;
an empty list is the constant monomial. Coefficients are exact integers.

## Reproduction and checking

Only the Python 3 standard library is needed. From this directory run:

```sh
python3 verify.py
python3 -O verify.py
python3 build.py --check
python3 render_appendix.py --check
```

`verify.py` independently expands each small circuit block, compares it
coefficient by coefficient with its source residual or its unit-pivot
rearrangement, and checks the row partition, acyclicity, final sum of
squares, degrees and coefficient bounds. It imports no producer. Its
seven negative controls confirm rejection of deliberately altered
circuits, domain labels and certificates. It calls the separate sparse
engine `expand_octic.py --check` to reconstruct all octic coefficients
and every variable-dependence certificate, then checks the printed tables.

The supplied receipts `VERIFICATION.json` and `VERIFICATION_OPTIMIZED.json`
record successful normal and optimized Python runs. No correctness check
depends on Python's removable `assert` statements.

To reconstruct all circuit JSON files from the source and pivot lists:

```sh
python3 build.py --output /absolute/path/to/new-circuits
```

To evaluate one polynomial at an explicitly supplied integer tuple:

```sh
python3 evaluate.py equations/integer125_degree16.json coordinates.json
```

`coordinates.json` must be a JSON list of 125 integers in that example.
`--modulus M` performs exact evaluation modulo M instead, when M > 1.
The evaluator does not search for solutions or decide consistency.

## Source binding and scope

`source/equation248.json` is the unchanged literal source, SHA-256:

```text
c51ebc12534db042bd1c7bf7c59f84602f51625e2d952dffa82fa054b5d92192
```

`SOURCE.json` records its provenance and the comparison repository
snapshot. In the integrating archive, `../direct_quartics/` retains the
fused front-sign proof and its predecessor proof closure. That material
is shared once rather than duplicated in this subpackage.

The checker establishes the new finite algebra; the inherited unbounded
C222/ZFC calibration is supported by those retained proofs and is not
re-proved by the Python program. This package is not an end-to-end
proof-assistant formalization. The elimination principle is standard;
the concrete polynomials, complete certificates and degree/dimension
tradeoffs are the new outputs. Code and exposition were developed with
AI assistance.
