# Reciprocal pooling across signed bases for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with `report/ConZFC_Mixed_Base_Pooling.pdf`. The complete standalone
LaTeX source is `report/ConZFC_Mixed_Base_Pooling.tex`; the editable section
source and generated appendices are also included.

## Result

The principal proposal is a fixed polynomial in **112 unrestricted integer
variables, of exact degree 24**. Its lack of integer solutions is provably
equivalent in ZFC to syntactic `Con(ZFC)`, by the new ordinary arithmetic
proof composed with the explicitly retained source calibration.

| Endpoint directory | Integer variables | Exact degree | Residuals | Expanded coefficient height bound |
|---|---:|---:|---:|---:|
| `integer143_degree8` | 143 | 8 | 80 | < 2^43 |
| `integer119_degree16` | 119 | 16 | 56 | < 2^79 |
| **`integer112_degree24`** | **112** | **24** | **49** | **< 2^79** |
| `integer107_degree32` | 107 | 32 | 44 | < 2^113 |
| `integer102_degree64` | 102 | 64 | 39 | < 2^214 |

All domains are unrestricted integers. The five equations use only fixed
integer constants and ordinary polynomial operations. The coefficient
heights above are rigorous upper bounds, not exact expanded heights. The
largest literal integer in the supplied evaluators is 60; expanded
coefficients are larger. Complete expansions of the larger final
polynomials are not claimed. Their exact finite circuits define every
coefficient without ambiguity.

Every polynomial is the sum of the squares of its explicitly supplied
residuals. The paper prints the complete original 153-residual source,
the exact 17-request interface, the new aggregate formula, and every
monic-elimination pivot. Those fixed tables are also a complete definition
of the final polynomials independent of Python.

## New mechanism and fair comparison

For each power block, let `T_j=2*A*n_j-n_j*n_j-1` and let `E_j` be the
explicit Pell error-norm numerator in the report. A single equation

```
sum_j E_j * product_(h != j) T_h - z * product_h T_h = 0
```

replaces all separate divisibility witnesses. A second integrality
argument rules out cancellation when the bases have opposite signs.
Zero bases are harmless because their modulus is -1. No coprimality
assumption is required.

Five blocks in source 172 use ten private coordinates. The raw fusion
replaces them by one, yielding a **207-variable degree-22** equation.
Exact acyclic monic substitutions then give the selected table above.
The same theorem applied to partitions of the five blocks gives the
lower-degree companions.

The fair matched degree-24 control already inlines the original three
moduli and two monic K coordinates, as well as the same 95 core
coordinates. It has **116 integers, 53 residuals, degree 24**. Fusion
gives **112 integers, 49 residuals, degree 24**, so its isolated gain
is four variables. The larger improvement against older packages also
uses a newer source and generic elimination.

The 143-variable octic is a useful generic-elimination companion with
five singleton pools. It does not need the new cross-base theorem.

## Proof boundary

The route directly encodes C222 and inherits its identified C222/ZF/ZFC
refutation calibration. It does not simulate K215 or instantiate Jones's
universal polynomial. Source 172's arithmetic proof and its restored
dependency tree are retained in `inherited/source172_signed/`.

The new theorem has a complete ordinary proof formalizable in ZFC, plus
separate AI-assisted reviews. The finite checks authenticate the literal
source, inverse witness maps, circuits, printed equations, exact degrees,
and dependence on every variable. They do not prove an unbounded theorem
by sampling, decide consistency, or constitute a new end-to-end Lean/Rocq
certificate. No global minimum or literature-wide priority is asserted.

## Reproduce

Python 3.10 or later and its standard library suffice. From the release root:

```sh
python3 -B verify.py
python3 -B -O verify.py
```

The verifier checks both independent algebraic auditors and reconstructs
all 36 emitted JSON files in a fresh temporary directory. It authenticates
the retained source files against their immutable provenance ledger.
To replay the complete retained arithmetic ancestry as well:

```sh
python3 -B verify.py --with-source
```

Write a fresh receipt outside the sealed extraction, if desired:

```sh
python3 -B verify.py --receipt ../new_receipt.json
```

The frozen polynomial inputs are `inputs/source216.json` and
`inputs/interface216.json`. The heuristic search is not needed to verify
any final polynomial; each chosen pivot list is fixed in
`inputs/monic_profile_*.json` and in the paper.

## Evaluate one tuple

Supply a JSON array of exactly the indicated number of integers:

```sh
python3 -B evaluate.py --equation integer112_degree24 --values tuple.json
python3 -B evaluate.py --equation integer112_degree24 --values tuple.json --modulus 1000000007 --residuals
```

This is evaluation, not a root search. A modular zero is not a consistency
counterexample. Variable names and the original source-coordinate map
are present in each `circuit.json`.

## Build the PDF

The standalone file compiles with ordinary pdfLaTeX and standard TeX Live
packages:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error ConZFC_Mixed_Base_Pooling.tex
pdflatex -interaction=nonstopmode -halt-on-error ConZFC_Mixed_Base_Pooling.tex
```

The generator `render_report_inputs.py` rebuilds the appendices and
standalone TeX from the canonical equation files. It is an authoring
command, so run it in a working copy rather than a sealed extraction.

## Integration

`INTEGRATION.md` gives a suggested repository entry. `SOURCES.json` and
`NOTICE.md` record attribution and comparison scope. The source snapshot is
`ef0c534c1ae1e312c61a2a9a5a3f18f5516fd42b`. No remote repository was changed
while preparing this contribution.
