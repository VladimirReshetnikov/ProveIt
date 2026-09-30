# Action Accumulation and Nonlinear Inversion

**A Laplace–measure calculus, hidden oscillations, and limits of Hardy-field realization**  
Research manuscript, 29 September 2026.

## Contents

- `action_accumulation_and_inversion.tex`: standalone, editable article source.
- `action_accumulation_and_inversion.pdf`: 29-page compiled article (28 as delivered) with proofs, numerical tables, bibliography, a formalization roadmap, and eight further research directions.
- `verify.py`: executable symbolic and high-precision numerical checks.
- `verification_results.json`: results from the recorded successful run.
- `SOURCE_NOTES.md`: repository snapshot, inspected documents, primary references, and retrieval limitations.
- `build.sh`: minimal reproducible PDF build.
- `requirements.txt`: the dependency versions used for the recorded checks.
- The delivered checksum ledger `SHA256SUMS.txt` was verified in full on filing (batch 46) and not kept; the delivered archive remains in the repository history (see `docs/incoming/README.md`, batch 46 row).

## Results developed in the article

The paper proves a composition and inversion calculus for exponentially weighted complex action measures, including accumulating supports with no positive action gap. It gives an explicit inverse measure, uniform truncation bounds, a compact-support rooted-tree majorant, and positivity and stability consequences.

The example A(x) = sum_{j>=1} j^(-2) exp(-x/j) has an exact Poisson–Bessel resolution. Its difference from 1/x has infinitely many zeros despite being smaller than every inverse power. The paper proves explicit finite-mode error bounds and a refined asymptotic location of the zeros, and derives Hardy-field and o-minimal obstructions. It then analyzes nonlinear inverses and exact zero transport. In the zero-gap, parameter-free example y = x + A(x), the inverse has a convergent Catalan asymptotic expansion but cannot belong to a Hardy field containing the identity germ.

Theorems are supported by human-readable mathematical proofs. They are not Lean formalizations. No exhaustive historical-priority claim is made, and no named general conjecture is represented as settled. The repository comparison is targeted, not a full audit of the large consolidated transseries volume.

## Build the article

A standard TeX Live installation with pdfLaTeX, Latin Modern, amsmath, hyperref, xurl, and the other packages named in the source is sufficient. No external images, private macros, or BibTeX run are needed.

```sh
sh build.sh
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error action_accumulation_and_inversion.tex` three times.

## Reproduce the checks

Requires Python 3.10 or later, `mpmath`, and `sympy`.

```sh
python -m pip install -r requirements.txt
python verify.py --output verification_results.json
```

The recorded environment was Python 3.13.5, mpmath 1.3.0, and SymPy 1.14.0. The script uses 120 decimal digits globally and 65 digits for the exact Bessel evaluations. It rejects a global precision below 110 digits because the independent Hurwitz-zeta evaluation is cancellation sensitive.

Checks include the core coefficient formula through coupling degree six, Catalan normalization through degree twelve, Bessel coefficients through degree eight, three independent Poisson–Bessel comparisons, finite and accumulating atomic inverse enclosures, a finite-measure composition test, and three finite-mode zero sign-bracket tests. All assertions passed in the recorded run.

**Numerical qualification:** these are high-precision floating-point consistency checks, not outward-rounded interval proofs. The analytical truncation inequalities are proved in the paper. Fully certified numerical endpoints would additionally require interval enclosures for all function evaluations and rounding errors. Finite numerical checks do not replace the proofs of the infinite statements.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 46 (see `docs/incoming/README.md`) with its
article unedited. The following changes were made afterwards; each change to
the article is marked in the source by a `% ed. (2026-09-29)` comment, and
every visible addition is an unnumbered "Editorial note (ProveIt,
2026-09-29)", so no theorem, section or equation number changed.

- `action_accumulation_and_inversion.tex`:
  - Preamble: the unnumbered `ednote` environment.
  - End of Section 2.1: a note giving the current paths of the inspected
    READMEs and of `Analysis/Transseries/Lean/Transseries/TransseriesWellBased.lean`
    (the article read them at their pre-split paths under
    `Analysis/FabiusFunction/`); naming the uncited repository passages
    the article enters — the companion volume's necklace accumulation
    (`t2:eq:necklace-action-accumulation`) and its third research direction,
    the inverse-harmonic package's problem "Arithmetic action accumulation
    rather than a discrete Borel lattice", and the canonical volume's
    action-one accumulation (`p3:sec:tail`, `p3:rem:no-eta-cutoff`); stating
    that the measure calculus is an analytic counterpart to them, not a
    resolution, because it drops the divisibility indicators; and naming the
    sibling `../Arithmetic_Transseries_Beyond_Accumulation_Cut/`, which
    keeps them and shares no theorem with this article.
  - After the remark following Theorem 10.3 (`thm:tameness`): the
    obstruction bears on the canonical volume's open
    `plt:rmk:ext-open-realization` but does not answer it (an analytically
    summed, non-well-based family, not a left-finite Hahn element).
  - Bibliography: `repo-group` and `repo-neumann` give the current paths
    first and the snapshot paths second.
- `action_accumulation_and_inversion.pdf`: rebuilt from the amended source
  (`latexmk -pdf`): 29 pages, no errors, undefined references, multiply
  defined labels, duplicate destinations or overfull boxes.
- `SOURCE_NOTES.md`: an editorial note after the list of inspected sources
  gives their current paths.
- `README.md`: the line listing the retired `SHA256SUMS.txt` is replaced by
  a sentence on its retirement.
- `verify.py`: the output JSON is written with `newline="\n"`, so a rerun on
  Windows no longer produces CRLF. A rerun of the amended program
  (`--output verification_results.json`; Python 3.13.5, mpmath 1.3.0, SymPy
  1.14.0) on a copy reproduced the filed JSON byte for byte.
