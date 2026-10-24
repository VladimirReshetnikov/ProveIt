# Scaled sign guards: twenty integers, degree eighteen

`equation.json` is a complete finite polynomial specification; `circuit.json`
is a 115-gate evaluator. All 20 coordinates range over unrestricted integers.
The polynomial is a sum of eight residual squares, exact degree18.

`PROOF.md` gives the complete two-way zero-existence reduction to the retained
source34 calibrated parent, the universal sign argument, all fixed-domain
qualifications and exact complexity certificates. The new idea multiplies a
sign quantity by a square already proved nonzero, then uses a retained linear
relation to lower its degree before eliminating two arithmetic coordinates.

The new point20/18/115 is a degree/cost tradeoff with the incoming20/20/111
point. It is not a global minimum or a fewer-variable record.

Reproduce with Python standard library:

```
python3 build.py
python3 check.py
python3 -O check.py
```

The parent and all six actual numeral payloads are retained under `parent/`.
`parent_ring.py` is a byte-identical copy of the parent's sparse-polynomial
checker. The new checker does not import the new builder, but it shares this
explicitly attributed upstream arithmetic engine; no independent-engine claim
is made. Normal and optimized receipts are supplied.

These finite checks certify the algebra and data. The sign lemma is proved
universally in the article. The final ZFC interpretation inherits the named
native/Pell/refutation calibration; no new Lean/Rocq or encoded internal-ZFC
proof is claimed.
