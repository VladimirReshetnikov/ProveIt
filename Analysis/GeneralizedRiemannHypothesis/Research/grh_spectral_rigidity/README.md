# Spectral rigidity of smoothed prime races

Research note, 26 November 2026.

Contents:
- `spectral_rigidity.tex` — self-contained mathematical exposition (with classical analytic number theory cited as prerequisites).
- `spectral_rigidity.pdf` — compiled manuscript.
- `verify_identities.py` — exact symbolic checks of algebraic identities and a synthetic shared-zero Gram example, using SymPy.
- `verification.txt` — recorded output of the symbolic checks.
- `SOURCES.md` — source audit and limitations.
- `FORMALIZATION.md` — proposed Lean development interface and dependency plan, not a verified implementation.
- `SHA256SUMS` — integrity checks for the above files.

## Reproduce
Run `pdflatex -interaction=nonstopmode -halt-on-error spectral_rigidity.tex` twice.
Run `python3 verify_identities.py` with SymPy installed; `sha256sum -c SHA256SUMS` checks the delivered files before regeneration.

The polynomial zero-divisor theorem is unconditional; high-pass covariance and oscillation use Dirichlet GRH. No upstream Lean build was performed here. No new Lean proof or numerical certification of actual zero multiplicities is claimed. The exact algebraic tests are supplemental, not substitutes for the proofs. The results were independently derived; priority has not been established.
