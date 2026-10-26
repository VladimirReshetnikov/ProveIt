# A CRT-anchor equation with a joint arithmetic certificate

Start with the [research paper](report/ConZFC_Direct_Integer_Elimination_2026-10-25.pdf).
Its editable [LaTeX source](report/ConZFC_Direct_Integer_Elimination_2026-10-25.tex)
and all required mathematical appendices are included in `report/`.

The recommended equation is `equations/integer85_degree16964.json`:
85 unrestricted integer variables, exact degree 16,964, 24 residual
squares, and 1,788 live binary additions, subtractions and multiplications.
Its lack of integer zeros is provably equivalent in ZFC to Con(ZFC),
using the explicit ordinary argument in `PROOF.md` and the identified
inherited C222/ZF/ZFC calibration. It contains no K215 simulation,
Jones polynomial, variable exponent, factorial primitive or unknown
coefficient. The lower-dimensional companion has 84 integer variables
at degree 2,097,732; the much larger degree is a genuine cost.

|Integer variables|Exact degree|Residual squares|Live binary operations|Expanded height bound|
|---:|---:|---:|---:|---:|
|109|32|48|1,895|at most 2^308|
|100|64|39|1,872|at most 2^390|
|90|256|29|1,819|at most 2^1297|
|88|444|27|1,807|at most 2^2149|
|87|956|26|1,804|at most 2^5093|
|86|1,092|25|1,797|at most 2^5341|
|85|16,964|24|1,788|at most 2^59805|
|84|2,097,732|23|1,775|at most 2^7342557|

The largest absolute literal integer in these graphs is 1,099,511,627,780,
inherited from package 173's affine growth multiplier. Literal size is
distinct from expanded coefficient height. Exact expanded heights and
monomial counts of these final high-degree polynomials were not computed.
The displayed bounds are proved conservative coefficient bounds.

## Definition

The frozen parent `source/anchor219.json` has 219 variables and 158 quadratic
rows. Its exact upstream bytes are separately retained as
`source/anchor219_upstream.json`; the working text has one additional
trailing newline. The polynomial and parsed JSON are unchanged.

The new joint-certificate source `joint209.json` retains 147 parent rows,
replaces eleven private coordinates and rows by one coordinate and one
degree-13 residual, and has exact degree 26 after squaring. Its full literal
request table and arithmetic proof are in `PROOF.md`. Each final equation
then eliminates selected unit-coefficient rows by acyclic polynomial
substitution. The JSON fields `elimination_steps`, `definitions`,
`retained_source_indices`, and `retained_source_rows` completely specify
that projection. Named gates are expression abbreviations, not unknowns.

## Verification and rebuilding

Python 3.10 or later with its standard library suffices:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B rebuild.py --output /tmp/conzfc-joint-rebuilt
```

The integrated `verify.py` retains the pinned source checks and runs four
independent finite checks:

- `code/verify_joint.py` checks all semantic ports, private restoration
  identities, the square frame, and all 66,371 collected terms of the
  new joint residual.
- `code/verify_projection.py` imports neither producer nor search. It checks
  every unit pivot, acyclicity, substituted node, retained row, final sum of
  squares, exact degree certificate, and genuine dependence on every input.
- `code/verify_report.py` independently parses the printed definition back
  into exact data. It checks all 147 printed source rows, the 85 free indices,
  the 124 ordered unit pivots, all 16 requests, and the eight profile rows.
- `research/affine_center_obstruction/verify_series.py` checks the exact
  rational Laurent coefficients supporting the auxiliary obstruction to
  affine scaling of the whole-product center. Its theorem concerns that
  specified polynomial family; it is not a global simplicity lower bound.

The projection and printed-definition checkers also reject deliberate
corruptions. The top-level verifier propagates Python's optimized mode to
every component, so both commands above exercise the full pipeline.
The rebuild recomputes the joint source and all eight final graphs from
the frozen parent and selected pivots, checking byte-for-byte equality.
These finite checks do not prove consistency or replace unbounded
number-theoretic and logical arguments.

Successful integrated receipts are retained in `verification_normal.json`
and `verification_optimized.json`. `rebuild_receipt.json` records the separate
successful byte-for-byte reconstruction of the source and all eight circuits.

To inspect the input order or evaluate the recommended polynomial modulo
a supplied integer:

```sh
python3 -B evaluate.py --variables
python3 -B evaluate.py --zero --modulus 1000000007
python3 -B evaluate.py --tuple tuple.json --modulus 1000000007 --residuals
```

Omitting `--modulus` evaluates over the exact integers, which can produce
very large values. A modular zero is not an integer zero. No supplied
program searches for a consistency witness.

## Rebuild the paper

The delivered LaTeX source already includes every required appendix file.
With TeX Live or another installation providing the listed standard packages,
compile from `report/` twice to resolve cross-references:

```sh
cd report
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error ConZFC_Direct_Integer_Elimination_2026-10-25.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error ConZFC_Direct_Integer_Elimination_2026-10-25.tex
```

If the generated definition appendices need to be recreated from the frozen
JSON data, run these commands from the package root before compiling:

```sh
python3 -B code/export_report.py
python3 -B code/verify_report.py
```

The exporter writes the metrics, free-index list, ordered pivot table,
literal request table, and complete source-row appendix. The independent
checker imports neither the exporter nor a polynomial producer. PDF metadata
and bytes can vary across TeX installations; the exact mathematical data and
parsed appendices provide the stable definition.

## Provenance and scope

This is a composition of package 173's relocated C-anchor/affine horizon
with package 176's simultaneous signed-index and power certificate,
followed by the existing acyclic monic elimination method. The comparison
snapshot is `ecb9a4b4dda617512952525d50f17343700aac52`. In particular,
the recommended 85-variable equation improves the placed package 177 direct
87-variable degree-8,388,612 point in variable count, degree and emitted
binary gates, with substantially larger literal integers. It is not
claimed globally simplest, novel relative to unread incoming ZIPs, or
literature-wide first. Other coefficient architectures have far fewer
variables; variable domains and coefficient costs remain distinct.

`inherited/` retains selected ordinary arithmetic arguments and the two
named Lean endpoint files. This is not their complete Lean import closure
and no fresh compilation of that closure is claimed. Historical validation
claims inside copied sources concern those earlier submissions. The new
argument was subjected to separately assigned AI-assisted mathematical
and finite-algebra review, not outside human peer review.
