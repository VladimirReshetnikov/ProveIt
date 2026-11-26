# Relative zeta zeros from compressed prime races

Research packet — 25 November 2026.

Read `report.pdf`; the complete editable manuscript is `report.tex`. This packet proves a classical analytic reduction, **not** nonabelian GRH. The geometric divisibility, short/enough/long forms and global congruence bounds required to establish the new prime-race inequality are open obligations. No novelty priority claim is made.

## Contents

- `report.tex` and `report.pdf`: precise theorems, proofs, source analysis, geometric transfer obligations and bibliography.
- `source-audit.tsv`: GitHub connector-returned Git object identifiers and source-reading scope, pinned to lsernau/grh-lean commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `checks/check_races.py`: standard-library Python exact permutation/stratum and modular-polynomial checks, plus floating-point diagnostics (not an asymptotic certificate).
- `checks/check_races.log`, `checks/quartic_race.csv`: outputs from the actual run in this environment. The polynomial is `X^4-X-1`; exclude prime 283.
- `checks/check_source.py`: optional Git blob-ID check against a local upstream clone; not run here, since the runtime could not download the checkout.
- `SHA256SUMS`: checksums for package members other than this manifest.

## Reproduce

Requires Python 3.8+ (do not use `-O`) and a TeX Live distribution with amsmath, hyperref, xurl, microtype, enumitem and booktabs.

```sh
python3 checks/check_races.py
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
sha256sum -c SHA256SUMS  # before rebuilding if verifying the original bytes
```

For the optional source audit, separately clone the public GitHub repository:

```sh
git clone https://github.com/lsernau/grh-lean.git
python3 checks/check_source.py grh-lean
```

The connector source inspection and published independent verification reports are not a substitute for a local Lean replay. No Lean compiler was present here. Four earlier ProveIt archive summaries/selected sections were examined; one larger archive returned empty content and the remaining archives were not exhaustively inspected. No GitHub repository was modified.
