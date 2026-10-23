# Sparse packing and arithmetic simplifications for Con(ZFC)

This archive specifies seven concrete integer-coefficient Diophantine
polynomials. In each stated witness domain, the ordinary mathematical
proof establishes, formalizably in ZFC,

    the polynomial has no zero  if and only if  Con(ZFC).

The polynomials and every fixed integer used in them are supplied as finite
artifacts. No consistency assumption is made, and no proof of the absence
of zeros or of global minimality is claimed. The contributions improve
explicit constructions in the pinned ProveIt collection by new sparse
packing, a packed successor translation, a smaller arithmetic square
separator, and a stronger auxiliary quotient congruence.

**Inspected repository:** `https://github.com/VladimirReshetnikov/ProveIt`.
**Pinned commit:** `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
**Prepared:** 2026-10-23.

## Frozen results

Operation counts refer to live binary `+`, `-`, and `*` gates in the literal
arithmetic circuits. Multiplication by a constant counts as a gate. Fixed
integer leaves are supplied separately; their bit complexity is not included
in the operation count. Degree is total degree in the quantified witnesses,
with the native coefficient ports specialized to their supplied integers.

| Equation and authoritative artifact | Witness domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `data/polynomial.json` | Unrestricted integers | 10 | 54,768,104 | 709 |
| `nine/generated/multitarget_nine_positive.json` | Strictly positive integers | 9 | 33,332,620 | 682 |
| `nine/generated/multitarget_nine_natural.json` | Nonnegative integers | 9 | 33,332,620 | 685 |
| `short/generated/p66_degree157.json` | Strictly positive integers | 15 | 157 | 66 |
| `short/generated/p68_degree113.json` | Strictly positive integers | 15 | 113 | 68 |
| `short/generated/p72_degree80.json` | Strictly positive integers | 15 | 80 | 72 |
| `short/generated/p74_degree68.json` | Strictly positive integers | 15 | 68 | 74 |

The first two direct prior comparisons are package40's ten-integer equation,
with degree 237,520,456 and 782 operations, and package45's nine-positive
equation, with degree 129,875,980 and 788 operations. The four short variants
improve the parent operation/degree pairs 67/155, 69/111, 73/80, and 75/68.
The 66-operation result trades two degrees for one operation; the two SOS
variants save one operation without increasing their degrees. Witness
domains are part of every statement and must not be interchanged.

The operation breakdowns of the main circuits are:

| Circuit | Additions | Subtractions | Multiplications |
|---|---:|---:|---:|
| Ten integers | 189 | 25 | 495 |
| Nine positive integers | 189 | 24 | 469 |
| Nine nonnegative integers | 195 | 21 | 469 |

Every circuit register is a polynomial abbreviation, not an additional
quantified variable. Every exponent in the definition is fixed. The JSON
circuits, fixed leaves, and coefficient manifests specify the equations
without requiring expansion into millions of degrees of monomials.

## Main ideas

**Sparse extraction targets.** The source contains 22 quadratic rows in
31 positive coordinates. Place each extraction target using that row's
actual support, while checking interference against all 528 quadratic
monomials that can occur in the dense packed square. The largest target
falls from 35,177 to 7,243 and the product support span from 36,775 to 8,841.
The exact target list and every exclusion check are supplied.

**Packed successor translation.** Encode positive source coordinates as
successors within the packed square: use `(1 + g + ell)^2` with the fixed
successor word `ell`, retaining the raw quadratic coefficients. This
reduces the weighted records from 136 to 94. The variable `g` itself remains
unchanged in the Sun/Lucas finalizer. The proofs verify the full input
ranges and carry bounds after this replacement.

**Arithmetic square separation.** The ten-integer finalizer uses weights
`1, b, bK`. A square-class argument, coprimality, and the specific Pell
radicands exclude cancellation. This replaces the much larger generic
separating multiplier. Exact algebraic sharing gives the final 709 gates.

**Squared-modulus auxiliary quotient.** In the short positive-variable
circuits, replace `c(T_old f - 1) - R f^2` by `f^2(cT - R) - c`. The literal
polynomial identity under `T_old = fT` proves soundness. A stronger
Chebyshev congruence modulo `f^2` constructs a positive new quotient and
auxiliary ordinate, proving completeness. It saves one gate in each of
four existing evaluators.

## File map

| Path | Purpose |
|---|---|
| `report/report.tex`, `report/report.pdf` | Integrated mathematical paper and compiled reading copy |
| `SOURCE_PROOF.md` | Sparse extraction, successor translation, positivity and range proofs |
| `FINALIZER_PROOF.md` | New arithmetic separator and ten-integer soundness/completeness |
| `nine/PROOF.md`, `nine/INDEPENDENT_REVIEW.md` | Nine-variable source interface, finalizer composition and independent review |
| `data/` | Ten-integer circuit, raw source rows, targets, weights and fixed-value manifest |
| `coefficients/payloads/` | Actual native package31 ports and the derived fixed leaves used by the main circuits |
| `coefficients/native31/` | Complete inherited package31 coefficient compiler, literal machine/tile tables, proof, payloads and notices |
| `nine/generated/` | Primary nine-variable circuits, equivalent degree-certificate circuits and audit receipt |
| `code/`, `nine/*.py` | Deterministic builders and finite verification programs |
| `certificates/` | Source, literal-formula, exact-degree, separator, interface and toy-control receipts |
| `short/` | Four short circuits, squared-modulus proof, complete package36 tuple and compiler, parent sources and audits |
| `upstream/` | Pinned inherited raw parent, compiler interface and Sun/Jones proof material |
| `upstream/JONES_DEPENDENCY.md`, `upstream/JONES_RATIO_LEAN/` | Exact inherited ratio theorem proofs, complete local Lean import closure and checked proof-status boundary |
| `SOURCES.json`, `short/SOURCE_PINS.json`, `provenance/COEFFICIENT_SOURCES.json` | Repository paths, commit identifiers and exact source hashes |
| `LICENSE`, `NOTICE.md`, subpackage `licenses/` and notices | Attribution and inherited license terms |
| `verify_all.py`, `verify_release.py` | Whole-archive and main-core verification wrappers |

The nine-variable degree-certificate circuits use 700/703 operations and
evaluate the same polynomials as the primary 682/685-operation circuits.
They expose a leading cancellation to establish the exact degree; they
are separate audit artifacts rather than the recommended evaluators.

## Fixed integers and provenance

The main ten- and nine-variable constructions use the **complete native
package31 tuple**, with bit lengths 1,064,921 (`beta`), 1,070,004 (`K`),
1,064,921 (`MC`), and 1,064,922 (`MF_source`). The source's derived fixed
leaves are also materialized and authenticated. The compiler that
regenerates the native tuple is included in `coefficients/native31/`.

The short constructions use the **complete package36 tuple**, with bit
lengths 1,012,115, 1,016,946, 1,012,115, and 1,012,116 in the same order.
Its entire compiler and independent coefficient audit are included under
`short/coefficients/`. All payloads are unsigned little-endian integers,
stored either directly or in gzip containers as specified by their
manifests. `MF_source` already includes the required high-mask shift.
The two tuples must each be used as a whole; individual ports cannot be
spliced between them.

The top-level source pins identify the inspected commit. Historical commit
identifiers inside verbatim inherited manifests are retained as provenance.
Original ProveIt, K215, Wade, and related notices are preserved in their
subpackage locations. New work is supplied under the accompanying ProveIt
MIT No Attribution license, subject to the retained third-party terms.

## Reproduction

From this directory, run:

```sh
python3 verify_all.py
```

Only the Python standard library is required. The wrapper authenticates
the copied coefficient sources, invokes the main-core verifier, rebuilds
both complete coefficient tuples, checks that the package31 output agrees
with the ports actually used by the main circuits, and regenerates all
four short circuits. It runs the designated independent checks under
Python's `-O` flag as well. All builders operate in temporary copies;
delivered files are preserved.

The release receipt was produced with Python 3.12.14. Python 3.10 or later
can run the mathematical checks, but gzip header behavior can vary between
versions and affect strict compressed-byte reproduction. Exact integer
payload hashes are recorded separately from compressed hashes.

For just the ten- and nine-variable core, run `python3 verify_release.py`.
For direct short-circuit and coefficient regeneration, follow
`short/README.md`; those direct builder commands write their stated outputs.

To compile the reading copy when a LaTeX installation is available:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Proof boundary

The new universal arguments are ordinary mathematics formalizable in ZFC.
They compose with the explicitly identified inherited native-window
compiler, K215 consistency calibration, Pell recovery results, Sun
integer finalizer, and Jones representation results. In particular,
the two Jones ratio theorems are actual theorem declarations with full
proof scripts in the included `NineRatio.lean`, and their 20-file local
import closure is included and pinned. This release has not rerun Lean's
kernel on that snapshot; see `upstream/JONES_DEPENDENCY.md` for the exact
source audit and external Mathlib dependency. No new complete Lean/Rocq
or object-language ZFC derivation from the released polynomials to Con(ZFC)
is supplied.

The finite programs check exact symbolic identities, literal circuit
implementations, fixed bytes, source support exclusions, gate liveness,
and exact degrees. Nonzero leading-coefficient certificates establish
that the reported degree upper bounds are attained. Toy examples and
modular diagnostics test implementation behavior; they do not replace
the universal arguments or decide Con(ZFC). The construction is a set
of explicit improvements relative to the pinned repository, with no
claim that a globally simplest Diophantine equation is known.
