# Residual bases and denominator engineering for ZFC consistency

Research iteration 18, prepared for Vladimir Reshetnikov, 25 October 2026.

Start with `report/main.pdf`. Its editable LaTeX sources are included. The package supplies literal polynomial equations, ordinary proofs, fixed numerals, inverse maps, independent finite checks and reproducible generators. No upstream repository was changed.

## Main results

All direct equations are quartics. Domain is part of each claim.

| Domain | Variables | Residuals | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|
| Unrestricted integers, dimension | 278 | 188 | 12,884 | 12,227 |
| Unrestricted integers, balanced | 279 | 189 | 5,483 | 7,200 |
| Unrestricted integers, sparse | 279 | 189 | 5,202 | 12,662 |
| Unrestricted integers | 284 | 194 | 4,270 | 10,864 |
| Unrestricted integers | 306 | 216 | 3,870 | 14,512 |
| Nonnegative integers, balanced | 229 | 179 | 5,607 | 65,892,965 |
| Nonnegative integers, smaller | 228 | 178 | 9,522 | 560,804,902 |
| Nonnegative integers, sparser | 228 | 178 | 7,512 | 2,445,412,949,744 |

The balanced 279-variable quartic improves the matched incoming 282-variable/192-row/5,491-term/height-128,446 equation on every varying listed metric. The 278-variable version buys one fewer coordinate at a support cost. These are direct C222 proof-calculus constructions, not overall variable records among all existing coefficient encodings.

- Ten strictly positive variables: operation/degree tradeoffs 77/626, 78/464, 79/460 and 80/384. Two dominated uniform-family controls are explicitly labeled.
- Fourteen unrestricted integers: degree 86 at 112 operations, or degree 94 at 110. The first improves degree 88/119; the second trades degree for evaluator length.
- Thirteen unrestricted integers: the identical degree-156 predecessor polynomial now has a 125-operation evaluator rather than 127.

## New ideas and attribution

1. Integer row operations expose affine consequences hidden in the quadratic residual basis. Unit-coefficient projection then removes coordinates exactly. Further residual-basis changes improve coefficient height/support without changing the zero set. Earlier coordinate shears are explicitly credited.
2. A shift-free descending-factorial certificate derives positivity from its existing equations before interpreting binomial data. It combines prior descending factorials and cofinal anchors, then benefits from reversible residual reduction.
3. Smaller transport denominators and partial normalization recover an index before recovering full divisibility. The earlier staged-denominator argument, unshifted coordinate, Pell doubling and native encoding are credited.
4. An odd sum coordinate combines a Pell root with a triangular positivity witness. A direct rational identity forces integral roots without a spurious zero-sum branch. Two compiler-only optimizations preserve the entire earlier polynomial.

The immutable comparison pin is ProveIt `e0c98c629bf10d30b695884f6b1d2ab361bdf513`. `reviews/baseline.md` gives exact comparisons and later source-status notes. Incoming placement alone is not mathematical acceptance. No literature-wide novelty or global minimum is claimed.

## Literal equations

- `quartic/ENDPOINTS.json` identifies each integer residual list, every collected coefficient and every inverse certificate.
- `natural/balanced229`, `natural/low_height228` and `natural/sparse228` contain the three complete natural residual lists and expansions. `projected229` is an intermediate control.
- `compact/*_v2.json` and `compact/*_bv.json` are finite arithmetic DAGs over exactly ten positive variables. Fixed coefficients are not unknowns; their complete coherent payloads and finite recipe are included.
- `roots/integer*.json` (excluding `_spec.json`) are the four complete unrestricted-integer DAGs. Their six-port tuple differs from the compact branch and must not be mixed with it.

A sparse term `[c,[i,j,...]]` means `c*x_i*x_j*...` with zero-based coordinate indices; `[]` denotes a constant. Every residual system defines a single polynomial as the sum of its residual squares. All circuits use only integer constants, variables, addition, subtraction and multiplication. No variable exponentiation, floor, factorial or binomial primitive remains in a final equation.

## Alternate coherent radix55 tuple

`compact_radix55/` supplies the same six free-port circuits specialized with the entire accepted radix55 four-port tuple. It is a different specialized polynomial, not an identical-polynomial rewrite or a mixture of ports. All counts and degrees remain the same. The credited source encoding reduces raw fixed-coefficient bytes from 295,388 to 242,484; no new encoding or printed-page saving is claimed. Its complete bridge proof, independent reconstruction and explicit tuple selection are included. `compact/` retains the original radix67 specialization.

## Replay

Python 3.10 or later and the standard library suffice:

    python3 -B verify.py

By default this authenticates the full inventory, makes separate disposable copies, and runs normal and optimized checks and rebuilds. The original package is not modified. Optional flags:

    python3 -B verify.py --mode normal
    python3 -B verify.py --mode optimized --receipt /tmp/replay.json

The top-level receipt records every successful stage, unchanged sealed bytes and rejected integrity corruptions. Component reviews explain the finer-grained algebraic checks and mutation tests. Failures are raised explicitly; passing a finite test is never used as a substitute for an unbounded proof.

To rebuild the report in a standard TeX Live installation:

    sh build_report.sh

The supplied PDF was rendered and visually reviewed. TeX-generated auxiliary files are not part of the sealed initial inventory; if you rebuild the report in place, use a fresh extraction for a strict inventory replay.

## Logical boundary

For every accepted endpoint, the ordinary mathematics composes new exact reductions with identified inherited arithmetic/refutation calibrations to establish in ZFC that absence of a zero in the stated domain is equivalent to Con(ZFC). This does not prove consistency or unsolvability. The new artifacts do not claim a fresh end-to-end Lean/Rocq certificate or an encoded object-language ZFC derivation. Independent reviews here are separate AI-assisted checks, not outside human peer review.

All source licenses, identities and dependency boundaries are retained. The previously disclosed leading-form omission in the inherited degree-44 proof is explicitly corrected in the root branch; the final new leading forms are independently checked against their literal circuits. Sealed prior archives were not modified.
