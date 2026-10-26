# Exact projections and unweighted joint pooling

All coordinates are unrestricted integers. Each equation is the sum of the
squares of its literal residuals; no search for coefficients or roots is implicit.

| Selected equation | Variables | Degree | Residuals | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| `integer138_degree8` | 138 | 8 | 78 | 12,099 | 1,125,899,906,842,624 |
| `integer114_degree16` | 114 | 16 | 54 | 127,818 | 16,250,018,885,420,533,678,080 |
| `integer113_degree16` | 113 | 16 | 53 | 1,030,202 | 16,250,018,885,420,533,678,080 |

The 138-variable equation is a generic exact projection. The sparse 114-variable
form uses the incoming unweighted mixed-base theorem. The 113-variable form
uses the new unweighted joint orientation-and-power theorem, plus an exact
retained-frame row operation. These are distinct variable/support tradeoffs,
not global optima. Coefficient heights are measured after complete collection,
not maximum literal circuit constants.

`control114_degree16` applies the identical 89 monic pivots to the unfused
three-base partition: 54 residuals, 1,008,268 collected terms, and the same
height. Thus the isolated new joint step saves one variable/row at unchanged
degree/height for about 2.2% more terms. This matched control is supplied as
**residual arrays, maps and measured metrics only**; its million-term collected
array is intentionally omitted. The verifier fully recollects it.

## Explicit equations and proof

- `equations/*/equation.json`: every residual coefficient and coordinate name.
- `equations/*/certificate.json`: every ordered integral unit-definition pivot.
- `NATIVE_DEFINITION.json` and `NATIVE_LEDGER.txt`: finite source-row substitution
  program and complete retained-index lists, suitable for a printed definition.
- `UNWEIGHTED_JOINT_POOLING.md`: complete ordinary arithmetic proof, including
  signed, zero and unit bases, noncircular classified indices, restoration,
  the exact numerator chart and the inherited calibration boundary.
- `seeds/*`: literal pool sources, actual ports and private-coordinate maps.

For each selected equation the ordinary proof, composed with the explicitly
bound source calibration, establishes in ZFC that absence of an integer zero
is equivalent to Con(ZFC). It proves neither consistency nor inconsistency.
No new end-to-end proof-assistant build or external human review is claimed.

## Coefficient format and chunks

`[c,[i,j,...]]` means c times the listed zero-based coordinates; `[]` is the
constant monomial. All indices within a monomial are nondecreasing.

The 138- and sparse 114-variable expansions are ordinary sparse arrays.
For `integer113_degree16`, `expanded_polynomial.json` is an explicit ordered
manifest with schema `chunked-sparse-polynomial-v1`. It gives every chunk's
relative filename, term count, SHA-256, first and last monomial, and the total
term count. Each `expanded/partNNN.json` contains a finite `terms` array.
Concatenate those arrays in manifest order. The verifier enforces strict
lexicographic monomial order across every boundary, no duplicates, every chunk
hash/count, and equality to the complete independently collected polynomial.
There is no duplicate monolithic copy. ZIP parts may place chunks in different
archives; extract all parts into the same directory before verification.

## Portable dependency and offline verification

This component must sit beside the delivered `signed/` component. Paths in
`SOURCE_BINDING.json` are relative to this component directory. Its copied
conservative affine209 source and certificate must match
`../signed/conservative209/` byte-for-byte. The sibling supplies the retained
ordinary proof and complete incoming Pell-growth210 closure. No network fetch
is needed. The new optional centered-frame sibling profiles are **not** used.

Python's standard library suffices:

```sh
python3 -B verify.py
python3 -B -O verify.py --deep
python3 -B build.py --check
python3 -B -O build.py --check
python3 -B build.py --output /tmp/reciprocal23-rebuilt
```

`evaluate.py EQUATION tuple.json` evaluates a supplied integer tuple without
searching. `witness_maps.py project|lift EQUATION tuple.json` implements the
explicit zero-set maps; it rejects nonzeros rather than asserting quotient
integrality on arbitrary tuples.

`verify.py` imports no producer for its independent seed/projection checks.
It checks all actual ports and restoration identities, every pivot and final
residual, all delivered coefficients, the control's measured recollection,
and deliberate pivot-corruption rejection. `--deep` also replays the sibling
signed checker. `build.py` separately regenerates all seeds, final residuals,
coefficient payloads and normative ledgers and compares their bytes.
These are finite coefficient checks, not tests that decide consistency.
