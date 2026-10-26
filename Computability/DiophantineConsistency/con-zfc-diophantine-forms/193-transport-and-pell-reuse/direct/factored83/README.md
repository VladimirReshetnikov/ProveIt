# Factored evaluator for the same 83-variable polynomial

This evaluator defines **exactly the same polynomial** as the frozen
`../P83/circuit.json`, at every integer tuple. It factors two long source
expressions and shares their square and quadratic norm. No variable,
residual, source theorem, projection, or zero-existence argument changes.

| Measure | Canonical evaluator | Factored evaluator |
|---|---:|---:|
| Unrestricted integer variables |83|83|
| Exact degree |624|624|
| Residual squares |31|31|
| Live binary operations |2,939|**1,789**|
| Multiplications in factored evaluator | |955|
| Additions in factored evaluator | |834|
| Largest absolute literal |324|**64**|
| Strict expanded coefficient-height bound |2^1568|2^1568|

The 1,150-operation reduction is about 39.1%. Each multiplication by an
integer constant and each square is charged. There is one extra node used
only by the complete source restoration, outside the final polynomial.
Gate values and restored source coordinates are expression abbreviations,
not extra quantified variables.

## Verification and rebuilding

Place this directory at `direct/factored83/`, with the frozen `source227.json`
and `P83/` in its parent. Python 3 and its standard library suffice:

```sh
python3 -B check_factored.py --rebuild
```

The default canonical directory is the parent. For another layout, supply
`--canonical-dir /absolute/path/to/direct`. The standalone builder accepts
the same option, and `--check` requires byte-identical rebuilding of the
graph, factorization expressions, and metrics.

`check_factored.py` imports no producer. It sparsely expands the two
factorizations in 227 independent source symbols, comparing all 336 and 154
terms with the exact original expressions. It checks both complete DAGs
against their restored source: every unit pivot, acyclicity, every retained
residual, and the final sum of squares. It then replays the degree and
83-input occurrence certificates and propagates the exact integer
coefficient-norm bound. The optional rebuild is additional to those
independent checks. `CHECK.json` records the actual successful run.

The canonical circuit's authenticated SHA-256 is
`b4c0637db413899337d66a10859dcd2e10dcc52feb283e398075b15d9e947c38`.
The factored circuit's SHA-256 is
`52fac5b2d51e84b9209003a1f41f44c2635f28e46dfd64336e8991150bd1d476`.

## Mathematical expressions

The complete factored formulas, in the same source-coordinate notation as
the article, are in `factored_evaluator.tex`. The residual numbered 28 uses
zero-based indexing and is retained source row 170. `factorizations.json`
gives their exact arithmetic syntax; `circuit.json` is the complete final
polynomial evaluator.

This is finite polynomial algebra. It neither strengthens nor replaces
the new unbounded Pell proof or the inherited logical calibration. It does
not assert consistency, unsolvability, or a globally optimal arithmetic
circuit.
