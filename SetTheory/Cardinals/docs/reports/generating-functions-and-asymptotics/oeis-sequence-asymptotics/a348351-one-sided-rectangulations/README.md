# Report 111 — A348351

This package contains the article `report111.tex`, its final `report111.pdf`, source-location records, and exact finite checks. The mathematical proof is in the article; the programs are finite validation, not proof assistants for the asymptotic probability arguments.

## Established results

For one-sided (area-universal) rectangulations, with Gamma=(7+sqrt(17))/2 and alpha=1+pi/arccos((-29+7sqrt(17))/4), the article establishes

- log a(n) = n log Gamma - alpha log n + o(log n)
- the ordinary generating function is not D-finite
- N(y) = log y/log Gamma + alpha/log Gamma log log y + o(log log y)

The multiplicative equivalent, positive amplitude, correction series, and transseries remain unproved here. Non-D-finiteness excludes a linear polynomial-coefficient differential equation for the generating function, equivalently a fixed-order polynomial-coefficient recurrence for the sequence. It does not exclude the exact multistate recurrence included in the article.

## Files and commands

Run from this directory with Python 3.10 or newer:

1. `python3 integrity.py` verifies the strict inventory and SHA-256 manifest
2. `python3 checks/verify_report111.py` runs exact finite validation
3. `python3 -O checks/verify_report111.py` checks the same guards under optimization
4. `python3 checks/mutation_campaign.py` exercises deliberate corruptions
5. `python3 build.py` builds the PDF twice in clean directories and requires byte identity
6. `python3 replay.py --archive /path/to/downloaded/report111_source_checks.zip --out /path/to/new-directory` performs a fresh full archive replay (the downloaded ZIP is external to its own extracted contents)

The checks use only the Python standard library. Building requires pdfTeX/pdfLaTeX and the TeX packages listed in the article preamble (including Latin Modern, AMS, microtype, geometry, enumitem, fancyhdr and hyperref). The script creates its TeX format in writable build storage when needed. It fixes the timestamp and suppresses variable PDF metadata. Exact byte identity is required for the same TeX installation; a different TeX version or font package can legitimately produce a different binary PDF.

No network access or third-party source PDF is needed for the replay. The linked primary references should be consulted to review the source bijection and the two external general theorems. Public URLs and exact cited locations are in `validation/sources.json`. No third-party source PDF is redistributed.

The manifest is an integrity record, not a digital signature or a mathematical correctness certificate. Regenerating it makes no authenticity claim. `seal.py` is the explicit packaging command; ordinary verification never rewrites the manifest.
