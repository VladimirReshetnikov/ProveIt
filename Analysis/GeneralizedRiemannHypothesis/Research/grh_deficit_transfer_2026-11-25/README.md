# Positive Frobenius deficits: a transfer beyond Dirichlet GRH

Research memorandum, 25 November 2026. Read `report.pdf` or edit `report.tex`.

**Status.** Written proofs of a one-sided averaged finite-difference zero detector, optimal nonnegative Frobenius weights modulo abelian class functions, a two-class S4 detector, and Kummer/automorphic applications. These results reduce further open RH statements and Artin's primitive root conjecture to explicit inequalities. The needed new arithmetic-geometric inequality is **not proved**. No claim of literature priority or of a new resolution of a major conjecture is made.

## Files

- `report.tex`, `report.pdf`: complete report and proofs, including source map and exact missing steps G1–G4.
- `source-audit.tsv`: source paths, connector-returned Git blob IDs, inspection scope. Tree identifier: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- `prior-audit.tsv`: four earlier ProveIt ZIPs whose selected contents were read through the GitHub connector.
- `checks/check_examples.py`: exact permutation, character, rational kernel, affine-group and polynomial-factor checks; illustrative floating-point diagnostics.
- `checks/run.log`, `checks/quartic_types.csv`, `checks/diagnostics.csv`: outputs actually produced by the script.
- `checks/check_source.py`: optional blob identity check on an upstream clone. Not run on an upstream clone here (network unavailable from runtime); the connector returned source text and IDs. It does not check Lean proofs.
- `SHA256SUMS`: digest manifest (verify before rebuilding).

## Reproduce

Python 3.10+ with SymPy and assertions enabled (do not run with `-O`):

```sh
python checks/check_examples.py > checks/run.log
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The finite examples are not asymptotic certificates. For source identity, obtain a local clone of https://github.com/lsernau/grh-lean, then:

```sh
python checks/check_source.py /path/to/grh-lean
```

The upstream Lean replay is a separate task with the repository's toolchain and Mathlib revision. This environment has no Lean executable, and the new mathematical proofs have not been formalized. No GitHub repository was modified.
