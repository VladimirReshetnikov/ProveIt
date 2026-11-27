# Exact prime cubature after adversarial erasures

Research packet, 27 November 2026.

- `paper.tex`, `paper.pdf`: theorem, proofs, sharpness example, provenance, bibliography.
- `SOURCES.md`: precise source inspection and limitations.
- `generate_certificate.py`: rational Gram-correction generator for a specific finite example; Python 3 + NumPy and SymPy.
- `certificate.json`: exact coefficient vector and list of removed primes (rational strings, not floating-point numbers).
- `verify.py`: independent standard-library verifier, including checks of the four parity-moment formulas in 906 parameter cases.
- `verification.txt`: observed verifier output.
- `SourceAudit.lean`: optional entry point for checking the upstream statements/axioms; not tested locally and not a formalization of the new results.

## Reproduce

    pdflatex -halt-on-error paper.tex
    pdflatex -halt-on-error paper.tex
    python verify.py

To regenerate the certificate (requires NumPy and SymPy):

    python generate_certificate.py
    python verify.py

The verifier checks every equality and inequality with exact rational arithmetic. The displayed decimal summaries are rounded. The certified example deletes about 2% of the baseline mass and is a particular adversarial choice, not proof of a universal 2% deletion guarantee. The general theorem uses only Dirichlet GRH and standard effective explicit-formula estimates, with a non-numerically-evaluated constant. Novelty is a proposed research contribution rather than a claim of verified priority.

To audit the formal input, from the vendored `grh` package with its own toolchain and built dependencies, run `lake env lean /absolute/path/to/SourceAudit.lean`.
