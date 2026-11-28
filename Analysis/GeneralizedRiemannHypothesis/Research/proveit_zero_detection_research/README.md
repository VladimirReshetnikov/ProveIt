# Exponentially smaller zero detectors for symmetric-group extensions

Research note for ProveIt, 27 November 2026.

## Results

- Resolves the smaller-detector question `nab:q:lowdegree` for every n >= 5, without assuming Artin holomorphy: a single field of degree below n!/2 suffices. The ternary code construction has degree n!/3^(r-d), r=floor(n/3), d=ceil(log2(r+1)), and is exponentially better asymptotically. It is optimal in the exponent among abelian subgroup detectors, up to polynomial factors. Its exact local multiplicity constant can be large; the result is a degree/zero-set reduction, not a claim of improved multiplicity for the smaller field.
- Improves the all-degree transposition-fixed field multiplicity estimate from 2(n-H_n) to C_n, with limiting ratio C_n/n strictly between 1.48335 and 1.48337. The general estimate uses the sign L-function order as a correction; Dirichlet GRH removes that correction in the open critical strip off the line over Q.
- Settles the sharp positive monomial cone identity `nab:q:un` in degrees 13 through 16, extending the repository's reported range through degree 12. All four certificates were checked in exact rational arithmetic. The all-degree sharp question remains open.

No new nonabelian GRH, Artin holomorphy, or one-sided nonabelian prime estimate is claimed. The upstream Dirichlet result was read at the statement/entry-point level, not rebuilt. The new paper uses standard Artin formalism, Brauer meromorphy and Hecke holomorphy. It is not Lean-formalized. Novelty is relative to the repository and a targeted literature comparison, not a claim of exhaustive priority.

## Contents

- `paper.tex`, `paper.pdf`: complete paper, 12 pages. Includes all human-readable proofs, exact certificate specification and references.
- `cert_13.json` through `cert_16.json`: exact positive rational combinations of monomial rows.
- `verify.py`, `verification.txt`: independent standard-library exact verifier and its recorded output. No optimizer, external libraries or character tables required. Also checks the exact enclosure for the asymptotic constant.
- `detector_examples.py`, `detector_examples.txt`: exact polynomial and Frobenius-weight computations with small-rank direct enumeration checks.
- `search.py`, `search_opt.py`: exploratory LP-based discovery programs, supplied for reproducibility of the method. Numerical LP only chooses candidate supports; rational verification is mandatory. Different solver versions/settings may produce different supports or no certificate within limits. The checked JSONs are authoritative; the search programs are unnecessary to verify them. Search may overwrite `cert_N.json`, so use a scratch copy.
- `SHA256SUMS`: integrity manifest for the substantive files.

## Verify and rebuild

Use Python 3.9+ (prefer 3.11+). Run from the extracted directory, without Python's `-O` option:

```sh
python3 verify.py
python3 detector_examples.py
sha256sum -c SHA256SUMS
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The search scripts optionally need NumPy, SciPy and SymPy. For example, run `python3 search.py 13 14 15 16` in a separate scratch directory and validate any produced certificate using `python3 verify.py cert_13.json` etc. The search is not a completeness test. The included `verification.txt` is the result of running the independent verifier on the supplied files, not a solver report.

## Source snapshot

ProveIt main: `6fc594264337ccd8deef0148bd9418d8f5a3dc49`.

https://github.com/VladimirReshetnikov/ProveIt/tree/6fc594264337ccd8deef0148bd9418d8f5a3dc49/Analysis/GeneralizedRiemannHypothesis/

Principal source: `Article/sections/nab.tex` (blob `7390a4bceb51e7ba358f3062398da5891c25db71`); `src.tex` (blob `f69668b2f95261630bb1282c2cc1f9c172b7e530`). The article describes its inherited Dirichlet RH/GRH input in `vendor/grh-lean`. Upstream pinned revision: `72fead102f663d5c7a407964a13dc0cf9d977207`. No repository files were modified.
