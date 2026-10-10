# Exact Relation Lattices, CM Class Products, and Zero Transitions

Research continuation prepared for Vladimir Reshetnikov, 10 October 2026.

The main deliverable is **article.pdf**. Its source is **article.tex** with
modular section files under `sections/` and references in `references*.tex`.
The package is designed for integration into the ProveIt polylogarithms
manuscript, without changing its baseline sources.

## Baseline

Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).

Pinned commit: `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`.

Source directory: `Analysis/Polylogarithms/docs/manuscript`.

The pinned collective manuscript has 228 pages. The provenance manifest
records hashes of the consulted source files. Novelty statements in this
continuation are relative to that baseline; classical ingredients are cited.

## Principal results

1. The all-odd-weight rank conjecture for the specified level-four imaginary
   product matrix is proved, with a stronger integral Smith-form theorem in
   every weight. Even-weight quotients have only elementary 2-torsion.
2. An explicit identity evaluates `Im Li_(w-1,1)(i,-1)` for every even weight,
   with a short integer row certificate.
3. A normalized CM resultant formula proves the five recorded weight-four
   class products and gives all-even-weight extensions, including explicit
   weight-six formulas. A genus refinement also proves the three recorded
   ratios and yields three explicit weight-six genus ratios. Exact modular
   polynomials are supplied through weight 24. A uniform theorem places all
   even-weight genus ratios in a fixed field of degree at most 12 over Q;
   the three worked discriminants have quadratic closure.
4. The positive zero counts of the fifth Stieltjes derivative family are
   exactly `3, 3, 5, 5, ...`; all zeros are simple. Every finite sign needed
   for this global theorem has an exact rational interval certificate.
5. The Lerch family has a complete small-positive-parameter zero
   classification. Odd-index first-derivative zeros move in alternating
   directions, and the index-three family has a proved nondegenerate fold.
6. Two local textual corrections and a detailed research agenda are included.

## Build and replay

Python 3.10 or later is recommended. Install the explicitly listed
dependencies if they are not already available:

```bash
python3 -m pip install -r requirements.txt
python3 code/verify_all.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The replay driver creates `replay/`, copies the scripts there, and writes
new receipts and logs without overwriting the delivered `data/` receipts.
It runs exact matrix checks through weight 13 and Smith forms through
weight 12, exact mixed-family row checks, exact modular weight-polynomial
checks through weight 24, CM interval certificates, and the rational zero
certificates. The CM and mixed-family scripts also perform explicitly
labeled numerical regressions; those regressions are not the proofs.

Run the slower numerical-only fold and next-index diagnostics with:

```bash
python3 code/verify_all.py --diagnostics
```

Regenerate the vector/PNG figure from the exact root brackets with:

```bash
python3 code/plot_n5_zeros.py
```

The commands are also exposed as `make pdf`, `make verify`, `make diagnostics`,
and `make figures`. The TeX build requires a normal LaTeX installation with
AMS packages, `latexmk`, `lmodern`, `microtype`, and `hyperref`.

## Evidence and limitations

The general rank and mixed-family theorems have finite symbolic proofs.
The general CM formula is deduced from classical modular and CM period
theory. The class-polynomial coefficients are certified by interval
evaluation combined with CM integrality. This certificate trusts the
directed interval elementary functions of `mpmath.iv`; it is not a formal
proof-assistant development.

The Stieltjes signs use only Python integer/rational arithmetic with explicit
logarithm and Euler–Maclaurin bounds. Completeness of the root count follows
from the proved global multiplicity bound and critical-point descent.

The fold location is a numerical diagnostic; its existence and
nondegeneracy have a separate analytic proof. The sixth- and seventh-index
first-derivative counts remain explicitly conjectural. The original `S_4`
mixed-relation conjecture and higher algebraic ladder conjectures remain open.

## Integration

Read `integration/INTEGRATION.md` and `integration/claim_ledger.json`.
`integration/text_corrections.patch` contains two narrow corrections to
the pinned manuscript. They concern a rank-difference implication and the
even-weight modified polylogarithm on real arguments. The patch does not
silently promote any baseline claim without its accompanying proof.

The article is organized into independent section files. The self-contained
zero preliminaries repeat established baseline material solely to make this
continuation independently readable; they can be omitted when inserting the
new sections into the original zero chapter.

`MANIFEST.sha256` records the delivered files. No repository commit or
publication has been performed by this package.
