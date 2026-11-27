# Local prime-power spectral detection

Research note, 26 November 2026.

## Contents

- `local_spectral.tex`: complete LaTeX article, with source audit, definitions, proofs, corollaries, prior-art discussion, and research questions.
- `local_spectral.pdf`: compiled eight-page article.
- `verify.py`: standard-library Python 3 verification of finite algebraic identities and primitive-character weights; numerical examples.
- `verification.txt`: actual output of `python verify.py`.
- `sample_values.csv`: 70 illustrative local prime-power sums and their square-root normalizations.
- `SOURCE_AUDIT.md`: inspected source identifiers and scope of verification.
- `SHA256SUMS`: checksums of the other included files.

## Reproduce

Run `python3 verify.py`. This checks 1,707 rational kernel/sign identities, independent finite character enumerations for 666 residue classes, and numerical consistency of the local and four-ramp sums. No external Python packages are needed. Then run `pdflatex -interaction=nonstopmode -halt-on-error local_spectral.tex` twice. TeX Live with standard AMS, geometry, hyperref, booktabs, microtype, and xcolor packages suffices. Check archive checksums before regenerating files if desired.

## Scope and novelty

The analytic proof uses standard classical Dirichlet L-function theory and a proved Landau lemma. The threshold theorem is independent of GRH; the square-root bound, critical endpoint density, and critical-line spectral formula specialize using the reported, independently machine-checked Dirichlet GRH theorem. The upstream Lean project was inspected but not rebuilt; no new Lean theorem has been compiled or claimed. The finite checks do not certify analytic arguments. The four-scale filter is closely related to prior work; the proposed contribution is the precise combination of a positive-part Mellin threshold, arbitrary fixed window width, primitive-conductor isolation, and uniform endpoint density and spectral recovery. Priority is not established.
