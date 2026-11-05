# Complement-packed Wang943 coefficients

This package replaces 41 separate parity fields by one aggregate
complement-sum decoder. It supplies a complete new tuple, with
`B=2^590069` and 295388 total raw bytes, versus `B=2^1012115` and 506664
raw bytes at the pinned comparison. The reduction is 41.6994% and concerns
the actual integer heights, not gzip representation.

The inherited 67-operation polynomial and 59-operation system are both
fully instantiated with the new tuple. Their arithmetic source, domains,
degrees, and witness counts are unchanged. No lower operation count is
claimed, and no other construction is silently rebound.

Read `PROOF.md` for the full decoder, native-interface, and actual-rank
controller proof; `native_report.tex`/`.pdf` contain the TeX exposition.
The literal equations are `retained16_system59.json` and `product67.json`.
`COEFFICIENT_BINDING.json` binds every fixed port and identifies the four
complete unsigned little-endian integers in `coefficients/*.bin.gz`.

Reproduce offline with Python 3.10 or later and its standard library:

    python3 build_coefficients.py
    python3 audit_coefficients.py

Compile the report from this directory with:

    pdflatex -interaction=nonstopmode -halt-on-error native_report.tex
    pdflatex -interaction=nonstopmode -halt-on-error native_report.tex

`SOURCE_PINS.json` fixes the repository commit, source paths, Git blob IDs,
and SHA256 hashes. Upstream material and attribution are retained under
`source/`, `licenses/`, and `NOTICE-upstream.md`. The independent auditor
does not import the builder and reconstructs all four complete integers
from the literal tile list.

The conclusion is ordinary mathematics formalizable in ZFC relative to
the explicitly inherited native compiler, Pell, and K215 calibration
theorems: unsolvability is equivalent in ZFC to Con(ZFC). This is not a
new end-to-end Lean/Rocq certificate or a decision of consistency.
