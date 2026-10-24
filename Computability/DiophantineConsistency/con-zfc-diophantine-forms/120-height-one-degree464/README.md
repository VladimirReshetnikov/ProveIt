# Coefficient height one and an eleven-integer degree-464 equation for Con(ZFC)

Research packet prepared for Vladimir Reshetnikov and ProveIt, 24 October 2026.

Start with **ConZFC_Height_One_and_Degree_464.pdf**. The complete editable
LaTeX source is `report/report.tex` and its four companion sections.

## Two concrete results

All final variables range independently over the unrestricted integers.

| Construction | Variables | Exact degree | Other exact metrics |
|---|---:|---:|---|
| Height-one quartic | **7,431** | **4** | **34,086 terms; every nonzero coefficient is +1 or -1; constant 1** |
| Centered eleven-variable equation | **11** | **464** | **122** live binary arithmetic operations |
| Direct eleven-variable companion | **11** | **488** | **121** live binary arithmetic operations |

Each equation comes with an ordinary proof, composed with its explicitly
retained source calibration, that ZFC proves its lack of integer solutions
equivalent to Con(ZFC). This is an equivalence, not a proof of consistency.
No new complete Lean/Rocq or encoded object-ZFC proof is claimed.

The coefficient-height-one construction is a new, independently checked
block-and-cycle compiler applied to the direct C222 proof-calculus source.
It uses neither a K215 simulation nor Jones's universal polynomial. Its
integer zero set is in explicit bijection with the supplied 519-variable
source system. The lifting map has degree at most two and preserves the
source sum-of-squares value on every source tuple, not only on zeros.

Height one is the least positive coefficient height possible for a nonzero
integer polynomial. The cost is extra variables: the incoming height-two
quartic has 3,564 variables. No overall simplicity optimum or worldwide
priority claim is made.

The eleven-variable construction combines the incoming coprime projection
and powered-saturation/interpolation arguments with a reduced guard and
shared center. It improves the matched centered equation from degree
688/126 operations to **464/122**, with the whole six-coefficient native
tuple unchanged. This branch retains the native/K215 calibration, unlike
the direct C222 height-one branch. Ten-integer equations and a 37-integer
native quartic already occur in ProveIt; these results do not supersede
their variable counts.

## Exact equations

- `height_one/output/polynomial.json`: every collected coefficient of the
  quartic, including an ordered description of all 7,431 coordinates.
- `height_one/output/polynomial.txt`: the complete equation in plain text,
  all 34,086 signed monomials, ending in `= 0`.
- `height_one/output/certificate.json`: every normalization, occurrence,
  product witness, agreement cycle, and unit anchor.
- `height_one/source/equation.json`: the unchanged 519-variable, 321-row
  integer source. Its sum of squares is the source polynomial.
- `height_one/source/reading/`: a curated offline source-proof supplement,
  with reading order, original source hashes, and explicit review boundaries.
- `eleven/powered_coprime11_aux.json`: complete degree-464 circuit.
- `eleven/powered_coprime11_direct.json`: complete degree-488 circuit.
- `eleven/coefficients/`: all six fixed integer payloads, bindings, and the
  finite reconstruction recipe. Coefficient ports are fixed numerals,
  not extra unknowns. `MF` is already shifted; do not shift it again.

For sparse polynomials, `[c,[i,j,...]]` denotes the integer coefficient `c`
times the listed zero-based coordinates. Repeated indices denote powers;
an empty list denotes the constant term. Circuit nodes are literal integer,
variable, or fixed-coefficient leaves and binary add/subtract/multiply
operations. There are no variable exponents, division gates, or opaque
norm operations in either final circuit.

## Reproduce offline

Python 3.10 or later and its standard library are sufficient. No network,
SymPy, or theorem prover is needed for the supported checks.

```sh
python3 verify_all.py
```

The runner authenticates the release manifest, works in a temporary copy,
runs both independent checkers in normal and optimized Python, checks
deterministic regeneration, and leaves the shipped files unchanged.
Optionally save a new replay receipt:

```sh
python3 verify_all.py --receipt /absolute/path/replay.json
```

The actual successful release receipt is `verification/RELEASE_CHECK.json`.
Its mathematical scope is explicit: exact finite algebra, coefficients,
graphs, and provenance are checked computationally. The unbounded Pell,
CRT, and consistency-calibration arguments are proved in the report and
cited source proofs; numerical testing does not establish those arguments.

Individual entry points:

```sh
python3 height_one/verify.py
python3 height_one/build.py --out /absolute/path/new-height-one-output
python3 eleven/check.py
```

The last individual command rewrites its local check receipt; the top-level
runner avoids this by using a temporary copy. To rebuild the PDF, run
`latexmk -pdf report.tex` from `report/`, or run `pdflatex` twice.

## Source and review boundaries

The comparison snapshot is ProveIt commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. The audit included current
incoming archives as well as the accepted research tree. Exact archive
paths, hashes, source members, and retained-file identities are provided
in the provenance and source-binding JSON files.

`review/` contains independent mathematical reviews within this AI-assisted
workflow. They are not external human endorsements. The source519
arithmetic calibration and the native source34 calibration are inherited
ordinary theorems, not newly formalized here. The report identifies both
interfaces and gives the new reductions in detail.

Further research questions concern reducing the height-one occurrence
count, sharing witnesses without collisions, reducing the dominant
eleven-variable radicands, and formally verifying the generic compiler
before tackling an end-to-end source calibration.

The archive contains all new polynomial data and all dependencies needed
to regenerate and independently check the new transformations. Historical
source files retain their original licenses and provenance. Their original
entry points are preserved as references and are not supported release
commands unless listed above.
