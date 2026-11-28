# Finite duality instead of iterative Fitting costs

A mathematical simplification proposal for the first-order congruence part of the readable RH/Dirichlet GRH Lean proof.

**Read `report.pdf` first.** The three substitutions use a finite-length annihilator to bound the relative Fitting cost, specialization at zero to produce a determinant of actual relation rows, and matrix-unit row packing to obtain an optimal block determinant. They preserve the existing common Ribet element valuation bound and all downstream contracts. They are not a new independent RH proof.

## Contents

- `report.tex`, `report.pdf`: standalone mathematical report and compiled PDF.
- `LEAN_PLAN.md`: exact interface-preserving migration and verification plan; not a compiled patch.
- `check_dual_fitting.py`, `checks.txt`: exact finite regressions and actual run output.
- `source_anchors.tsv`, `proposal_audit.tsv`, `proposal_tex_scan.tsv`, `verify_sources.py`: source and proposal provenance, with optional local Git verification.
- `SHA256SUMS`: checksums of all package contents except itself.

## Reproduction

```sh
latexmk -pdf -halt-on-error report.tex
python3 check_dual_fitting.py
sha256sum -c SHA256SUMS
python3 verify_sources.py /path/to/ProveIt
```

The source verifier expects the pinned commit `9050b04000647d588d0c78d945180abcd3b0bcf7` to exist in a local Git checkout. It uses Git object IDs, not network access. The checked source hashes were obtained via GitHub; the verifier is supplied for local reproduction and was not run against a full checkout in this session.

## Status

The three general replacements have mathematical proofs in the report. No new Lean code was elaborated or kernel-checked, and the baseline was not rebuilt. The baseline project reports independent verification, but whole-tree identity with the externally checked version was not established here. No repository files were changed. The proposal audit covers 18 directory summaries and a targeted keyword scan of all 28 TeX files. This is not a line-by-line proof review or global priority claim. No measured net code-size or build-time reduction is claimed. The proposed changes simplify local arguments in roughly 200 existing source lines, not a large fraction of the entire proof.
