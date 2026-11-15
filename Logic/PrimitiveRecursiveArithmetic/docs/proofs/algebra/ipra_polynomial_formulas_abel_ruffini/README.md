# Radical formulae through degree four and Abel--Ruffini in iPRA

This archive contains a human-readable constructive proof, an arithmetization
plan for intuitionistic primitive recursive arithmetic, and a Lean
formalization roadmap.

## Main files

- `main.pdf` - compiled report.
- `main.tex` and `chapters/*.tex` - LaTeX sources.
- `certificates/verify_certificates.py` - exact symbolic and finite checks.
- `certificates/verification_report.json` - generated check results.
- `Lean/IPRAAbelRuffiniBlueprint.lean` - import/interface blueprint.
- `BUILD_INFO.txt` - pinned source and build environment summary.
- `MANIFEST.txt` and `SHA256SUMS` - archive inventory and integrity hashes.

The report is pinned to ProveIt commit
`25da87848ad4042c318af9bbc7f2e1c24614d6c3`.

## Build

```bash
python3 -m pip install -r requirements.txt
make
```

`make check` uses exact SymPy arithmetic. `make pdf` requires a standard LaTeX
installation with `latexmk` and the packages named in `main.tex`.

## Formalization status

The referenced ProveIt Lean files already kernel-check the field-generic
formula identities and semantic Abel--Ruffini results. The new end-to-end iPRA
bridge in this archive is a detailed blueprint, not yet a completed Lean proof.
That distinction is stated explicitly in Chapter 11.
