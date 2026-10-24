# Thirteen integer variables for Diophantine ZFC consistency

**Main result: a fixed ordinary polynomial in 13 unrestricted integer unknowns,
exact degree 1,392, with a 475-operation arithmetic circuit.**

The mathematical proof composes the new reductions with the explicitly retained
ProveIt native/compiler and literal K215 calibration. It establishes, by ordinary
mathematics formalizable in ZFC, that the equation has an integer zero exactly
when the fixed syntactic ZFC calculus has a finite refutation. Therefore its lack
of integer zeros is provably equivalent in ZFC to `Con(ZFC)`.

Start with `report/report.pdf`; the complete, standalone LaTeX source is
`report/report.tex`.

## Results

All domains in this table are **unrestricted integers**, including negatives and
zero. Operations count live binary additions, subtractions and multiplications;
squares and multiplication by fixed numerals are charged. Numeral leaves and
register reuse are free. Registers are polynomial abbreviations, not additional
quantified variables.

| Literal equation | Unknowns | Exact degree | Operations |
|---|---:|---:|---:|
| `forms/integer13_degree1392.json` | **13** | **1,392** | **475** |
| `forms/integer13_degree1408.json` | 13 | 1,408 | 473 |
| `forms/integer14_degree652.json` | **14** | **652** | **230** |
| `forms/integer14_degree664.json` | 14 | 664 | 223 |
| `forms/integer14_degree700.json` | 14 | 700 | 217 |
| `forms/integer14_degree748.json` | 14 | 748 | 215 |
| `forms/integer15_degree214.json` | **15** | **214** | **139** |

The comparison snapshot is ProveIt commit
`cfbf118b4ad9b2c651fe96b571d9415261766328`, including packages 31–75 and the
incoming archives. The preceding modest-degree unrestricted-integer frontier
included 17 variables at degree 88. A named prior 13-integer form has degree
10,461,744. Existing 10-integer equations retain a better variable count at much
higher degree; positive-variable results use a different domain. No global
simplicity optimum or worldwide priority claim is made.

## The new mechanism

If nonzero rational radicands have pairwise distinct even valuations at a fixed
prime, a rational signed sum of their square roots forces every root to be
rational. Inside one square class, a unique least valuation prevents cancellation;
distinct square classes are linearly independent over the rationals. This works
for signed radicands as well.

The construction arranges five base radicands to be units at 3 and weights their
roots by `3H`, `9H`, `1`, `81H`, and `27H`. Four roots enforce Pell conditions.
The fifth enforces positivity through the classical three-generalized-pentagonal
identity. Its use here is new within the inspected repository; the pentagonal
theorem itself is attributed to the classical literature.

The denominator `delta=Q-1` is nonzero before positivity is known, by its residue
modulo 3. Positivity is recovered from the fifth square; only then is rational
Pell descent used to restore the auxiliary integer root. This order matters.
The normalized strong witness is selected explicitly at Pell index `R*c`, so
completeness does not assume an unproved cofinality condition.

The supplied five-root norm is fully expanded into a **division-free arithmetic
DAG**. There are no radicals, variable exponents, hidden quantifiers, or runtime
proof-search calls in the literal polynomial.

## Reproduction

Python 3.10 or newer, standard library only:

```sh
python3 verify.py
python3 -O verify.py
```

Rebuilds and diagnostic runs use temporary copies. The root replay authenticates
the release and inherited sources, regenerates every native coefficient, checks
all seven graphs against their builders, verifies exact degree certificates and
operation counts, independently compares the article's main equation with a
multiquadratic-ring evaluator, runs the normalization/positivity diagnostics,
and exercises corruption controls. It does not search for a ZFC refutation.

An optional receipt can be written outside the sealed tree:

```sh
python3 verify.py --output /absolute/path/replay.json
```

From `report/`, rebuild the PDF by running twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Proof status and fixed coefficients

The new arithmetic reduction has ordinary unbounded proofs and independent
AI-assisted mathematical reviews. Exact finite checks supplement those proofs.
The inherited native/compiler and K215-to-refutation calibration is a named
mathematical dependency, with the immediate parent archive and key source
proofs retained. This is not a new end-to-end Lean/Rocq certificate, an exported
derivation in ProveIt's encoded object-language ZFC calculus, or external peer
review. The report explains these distinctions.

All six coefficients are actual fixed numerals. The four native ports form the
complete source34 mixed-parity-unrounded-1064921 tuple; `MF` is already shifted.
The two determinant scales are `2^1113` and `2^666104`. Their payloads total
615,883 uncompressed bytes. Copies under `forms/coefficients/` make that component
self-contained and are checked against the authoritative root `coefficients/`
values. No source31 or compact44 ports are substituted.

The package does not claim a smaller maximum expanded coefficient, a smaller
expanded monomial count, or an optimal arithmetic circuit. The exact degree,
variable count, graph size and fixed numeral payload are separate measurements.

## Contents and incorporation

- `report/`: complete article in LaTeX and PDF.
- `forms/`: seven literal equations, deterministic builders, norm templates,
  exact degree proofs, and independent algebra checkers.
- `coefficients/`: fixed numerical payloads, complete native construction,
  literal machine and tile data.
- `proofs/`: normalization and positivity proofs and independent mathematical
  reviews of the new reductions.
- `upstream/`: immediate source archive, exact 17-integer parent, inherited
  calibration and comparison texts.
- `code/`, `checks/`: adapter diagnostics and finite verification receipts.
- `SOURCE_PINS.json`, `MANIFEST.json`: immutable input identities and release
  integrity records.

This can be incorporated as a new research package beside the existing
`Computability/DiophantineConsistency/con-zfc-diophantine-forms` proposals.
Choose the numerical prefix at incorporation time. The existing formal endpoint
is not modified. Historical relative links inside verbatim upstream sources
refer to their original locations; the new root commands above are the supported
replay interface.
