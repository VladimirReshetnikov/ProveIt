# Cofinal descending certificates: direct quartics over naturals

Every coordinate independently ranges over **N={0,1,2,...}**. The equation in
each selected directory is the sum of squares of its literal quadratic rows.

| Endpoint | Variables | Rows | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|
| natural219 | 219 | 171 | 8,267 | 130,686,428 |
| sparse221 | 221 | 173 | 5,253 | 65,867,916 |
| balanced221 | 221 | 172 | 5,586 | 65,892,620 |

The new mathematical step takes the **even horizon** `t=2*t0+4` and the
**cofinal beta bound** `y=V-1`, where `V=(F²-1)^t` is an existing certified
power. Even parity makes `t!` divide `y`; proof-tree pending products are all
smaller than `V`, so the beta CRT construction remains complete. This combines
with the shift-free descending factorial, positive deterministic Pell center,
four pooled digit budgets, and a derived factorial-output bound.

The horizon substitution is **not a natural-coordinate bijection**. Its new
natural-domain theorem is proved separately. All later contractions have
explicit nonnegative restoration certificates. Final residual-row shears are
reversible and do not change any coordinate or its domain.

Relative to the retained ordinary C222/ZF/ZFC calibration, each polynomial has
a natural zero iff a finite syntactic ZFC refutation exists. Thus ZFC proves
its no-zero statement equivalent to Con(ZFC). This is not a consistency proof,
global minimum, or newly kernel-checked end-to-end logical endpoint.

## Verify and reproduce offline

Python 3.10+ and its standard library suffice, from any working directory:

```sh
python3 -B /path/to/natural/verify.py --rebuild
python3 -B -O /path/to/natural/verify.py --rebuild
```

Verification is read-only unless `--output RECEIPT` is explicitly requested.
Rebuilding uses temporary directories and needs no network. It independently
checks source edits, coefficient translations, natural restorations, forward
and inverse row maps, every collected coefficient, refreshed metadata and
rendered TeX. Deliberately corrupted inputs are rejected. The complete retained
Round18 compiler and source closure is also verified/rebuilt.

## Files

- `PROOF.md`, `COFINAL_PROOF.md`, `report_section.tex`: complete new ordinary
  arguments and a report-ready TeX section.
- `raw/`: positive-center/four-pool composition of the descending source.
- `cofinal_raw/`: new even-horizon cofinal source and its exact mutation receipt.
- `natural219/`, `sparse221/`, `balanced221/`: selected final equations.
- `dimension219/`, `cofinal221/`, `projected221/`: pre-row-basis controls and
  exact natural-contraction certificates; the first also has its priority list.
- `inherited/`, `SOURCE_MAP.json`: pinned source/compiler/proof closure and
  attribution. Historical endpoint counts in inherited documents refer to
  their historical equations, not these new endpoints.

A term `[c,[i,j,...]]` means `c*x_i*x_j*...`; `[]` denotes a constant. Complete
ordered coordinates are in `variables.tsv`, residuals in `residuals.tex` and
`residuals.txt`, and every expanded SOS coefficient is in
`expanded_polynomial.json`. No symbolic power/factorial/binomial operation
remains in those literal coefficient lists.
