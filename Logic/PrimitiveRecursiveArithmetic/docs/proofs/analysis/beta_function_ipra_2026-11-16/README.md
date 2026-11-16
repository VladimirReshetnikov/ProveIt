# Beta function in intuitionistic primitive recursive arithmetic

Prepared 16 November 2026.

## Main report

- `paper/beta_function_ipra.pdf` - compiled research report.
- `paper/beta_function_ipra.tex` and `paper/sections/*.tex` - complete LaTeX sources.

## Formalization material

- `lean/BetaIPRAOutline.lean` - a detailed Lean/ConciseIPRA formalization skeleton. It is intentionally an outline with explicit `sorry` obligations and is not claimed to compile as delivered.
- `lean/FORMALIZATION.md` - dependency order, object-theory targets, and proof-status audit.

## Exact finite artifacts

- `code/beta_finite_certificates.py` - exact-rational checker for finite identities used in the report.
- `evidence/finite_certificates.json` - generated certificate record.
- `evidence/theorem_inventory.csv` - source formula inventory and constructive status.
- `SOURCE_MANIFEST.md` - references and inspected ProveIt paths.
- `SHA256SUMS.txt` - checksums.

## Rebuild

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error beta_function_ipra.tex
cd ..
python3 code/beta_finite_certificates.py --output evidence/finite_certificates.json
```

## Scope and status

The report gives human-readable constructive proofs and a detailed route to internal `Prf PRAAx` derivations. It does **not** claim that the complete analytic development has already been checked by Lean. The current ProveIt repository's `ConciseIPRA` and `Derivations` libraries are checked; its analytic proof packets, including the Gamma packet reused here, are research packets with explicitly uncompleted analytic/object-theory obligations.
