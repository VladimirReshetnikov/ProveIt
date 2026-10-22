# A 27-integer Diophantine formulation of Con(ZFC)

This package synthesizes the ProveIt snapshot
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035` and supplies three improvements.

| Form | Unknowns | Equations | Exact degree | Binary operations |
| --- | ---: | ---: | ---: | ---: |
| Positive polynomial | 13 positive integers | 1 | 515 | 84 |
| Positive system | 13 positive integers | 4 | 488 maximum | 78 |
| Integer polynomial | 27 unrestricted integers | 1 | 1004 | 139 |
| Integer system | 27 unrestricted integers | 4 | 952 maximum | 133 |

The fixed compiler alphabet has 5,268 tiles, with `B=2^(5^17)`, improving
the previous 37,075-tile `B=2^(5^18)` instance. The complete coefficient
tuple is specified by `COEFFICIENT_BINDING.json` and
`compiler/pruned_t4_constants.json`; its enormous integer entries are
specified exactly by finite formulas and are not expanded.

## Mathematical statement

Using the repository's ordinary K215 calibration and native/Pell compiler
theorems, ZFC proves that the corresponding equation has no solution in
its stated domain if and only if Con(ZFC). The new mathematical proofs are
in `report.tex`, `report.pdf`, and `proofs/`.

The 27-integer polynomial is

`P27 = N1 Nk Nt (1 + Res) - 1`,

with every register defined explicitly in the article and the circuit JSON.
Seven positive intermediate coordinates use
`Pos(x,y,z)=x*x+x+y*y+z*z+1`; six other coordinates are unrestricted.
The three eliminated Pell roots are recovered by a proved rational-square
argument. The proof separately excludes all possible zero denominators.

The new smaller weight `I^2+v^2` also improves the 13-positive-variable
construction from degree 571 to 515 at the same 84-operation cost.
The integer form trades increased degree for two fewer variables; it does
not dominate the older 29-integer degree-188 form in every metric.

## Reproduce

Python 3 with its standard library is sufficient:

```bash
python3 verify.py
```

This regenerates all four circuits, the ordered compiler tile list, the
fixed coefficient recipe, and finite audit receipts. No network access,
third-party Python modules, expanded enormous coefficients, or unknown
K215 halting computation is required. `verification/summary.json` records
the combined result. The checks test exact algebra and finite compiler
facts; the ordinary proofs establish the unbounded statements.

To rebuild the article with a standard LaTeX installation:

```bash
make pdf
```

## Contents

- `report.tex`, `report.pdf`: comprehensive article and proofs.
- `data/`: four explicit division-free straight-line programs.
- `src/`: construction and independent algebra checks.
- `compiler/`: exact machine table, 5,268 literal ordered tiles, coefficient
  recipe, and finite geometry/carry/overlap checker.
- `proofs/`: new proof notes and independent reviews.
- `upstream/`: pinned arithmetic inputs and substantive imported proofs.
- `SOURCE_PINS.json`: provenance and hashes of imported sources.
- `COEFFICIENT_BINDING.json`: the single complete default tuple and exact
  mapping to the four circuit constant ports.
- `verification/`: checked receipts and document review.
- `MANIFEST.sha256`: delivered-file checksums.

The proof-assistant-verified object inherited from the repository is the
machine endpoint. The new Diophantine and compiler results are ordinary
mathematical proofs, not new Lean/Rocq artifacts. There is no proof of
Con(ZFC), no accepting K215 computation, and no claim of global minimality.

Suggested placement: a new numbered package under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`.
Keep the older packages and their distinct tradeoffs intact.
