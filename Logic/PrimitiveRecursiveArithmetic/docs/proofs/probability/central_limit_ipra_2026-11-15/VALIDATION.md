# Validation and build status

## Mathematical reference program

Command:

```sh
python3 code/finite_clt.py --output code/validation.json
```

Recorded result:

- status: `passed`
- exact integer/Fraction assertions: `75`
- floating-point regression diagnostics: `39`

The exact checks cover finite-law normalization, convolution means and
variances, iid sum moments, Lyapunov-to-Lindeberg inequalities, the rational
constant audits for `7` and `64`, the pairwise-independence counterexample,
the Lindeberg/non-Lyapunov row, and the rare-spike `n=30` example.

The floating checks compare finite exact distributions with numerical normal
CDF/local-normal values. They are diagnostics only; they are not used as
proof oracles and are excluded from the exact assertion count.

## PDF

- output: `paper/central_limit_ipra.pdf`
- pages: `32`
- paper size: A4
- encryption: none
- PyMuPDF open check: passed
- scanned-image heuristic: false
- unresolved LaTeX references: none
- overfull boxes: none
- remaining typography diagnostic: one harmless underfull box in the
  quantifier-free-invariant table

All 32 pages were rendered at 200 dpi and visually inspected in contact
sheets. No clipping, overlap, black boxes, missing glyphs, or broken tables
were observed.

See `validation/pdf_preflight.txt` and `validation/latex_diagnostics.txt`.

## Python and Lean-facing files

- `python -m py_compile code/finite_clt.py`: passed
- declaration scan: no `axiom` declarations or `sorry` proof terms found in
  `lean/`
- Lean compilation: **not performed** because `lean`, `lake`, and `elan` were
  not installed in the preparation environment

The Lean artifacts are therefore design blueprints. They are not claimed to
elaborate or to constitute a kernel-checked iPRA proof. The unfinished endpoint
is explicitly represented by the missing concrete checker `beTest` and the
missing value `CentralLimitIPRAPlan.InternalProof beTest`.

## Trust boundary

The manuscript supplies the completed human-readable mathematics for the
stated finite/effective hypotheses. The Python program provides finite
regression checks, not a universal proof. The Lean files specify a path to a
deep object-language derivation, but that derivation has not yet been
implemented.
