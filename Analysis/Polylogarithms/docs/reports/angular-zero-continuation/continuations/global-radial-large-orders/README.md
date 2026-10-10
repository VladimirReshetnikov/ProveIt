# Global Radial Monotonicity for Harmonic Polylogarithms

Research continuation for Vladimir Reshetnikov's ProveIt project, 10 October 2026.
Reviewed repository reference: `3338e535ef54ad8f6be56bdce8b3d084a2924465`.

## Main contribution

For `F_(a,b)(z) = sum_(n>m>=1) z^n/(n^a m^b)`, let theta be the unique upper-semicircle zero of its imaginary part and eta(rho)=cos(theta)/rho.

The article proves **strict decrease on the whole radius interval `0 < rho <= 1` for every real `a >= 8`, every `b > 0`**, including the differential bound

`eta'(rho) < -rho * H_4^(b) * (2/5)^a / 120`.

A separate theorem proves the same direction for every `a > 0` whenever

`2^(-b) < ((2/5)^a - (3/8)^a)/256`.

For integer outer orders 1 through 7, sufficient integer inner-order thresholds are respectively 14, 14, 15, 16, 17, 18, 19. These are sufficient, not sharp. The original integer conjecture for `a >= 2` is thereby reduced to six bounded strips with `a = 2,...,7`.

The article also gives a positive squared-resolvent measure, a weighted cubic-moment criterion for radial velocity, positive binomial identities with exact errors, and explicit specializations for pi log(2) and Dirichlet beta differences.

## Read and reproduce

`article.pdf` is the compiled article. `article.tex` contains its editable source and bibliography. Read `CLAIM_STATUS.md` for precise boundaries and `CORRECTIONS.md` for the targeted audit.

Run all exact certificates with Python 3.10 or newer:

```sh
python code/run_all.py
```

No third-party Python package is required. Do not use `python -O`; the scripts explicitly reject optimized mode. The scripts regenerate receipts in `data/`, so replay on a copy when preserving delivered evidence bytes matters.

Rebuild the PDF using a standard TeX Live installation with newpx, amsmath, amsthm, microtype, hyperref, cleveref, and the other ordinary packages listed in the preamble:

```sh
./build.sh
```

On Windows, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times. No BibTeX or network access is needed.

## Recorded checks

The delivered replay passes exact checks for ten positive rational Bernstein coefficients, the three uniform sums with analytic tails, eight angular-root brackets, nine Gaussian-value enclosures, 720 positive finite binomial moments, 100 finite polynomial remainder identities, and the stated sufficient inner-order thresholds. The `(a,b)=(1,1)` Gaussian enclosure also contains an independent rational enclosure for pi log(2)/8.

The eight root brackets are illustrative independent certificates. The global theorem is proved by uniform inequalities, not by sampling those eight points.

## Integration

This package makes no remote repository changes. Suggested report location:

`Analysis/Polylogarithms/docs/reports/global-radial-monotonicity/`

`integration/05-global-radial-monotonicity.tex` is a namespaced additive excerpt; `integration/INTEGRATION.md` explains its dependencies and the required status updates. The full analytic proofs remain in the article.

## Scope

The complete normalized-radius conjecture is **not** claimed proved. The remaining bounded strips for integer `a=2,...,7`, the first-order cases not covered by the large-inner-order theorem, and the arithmetic S6/S8 candidates retain their open status here. Fractional local turning-point results in prior incoming work are neither contradicted nor repackaged as new results.

The proof is an ordinary mathematical argument with finite exact arithmetic certificates. It is not proof-assistant formalized, externally refereed, or accompanied by a literature-wide priority claim. The source audit is targeted: the relevant manuscript files and accessible incoming scope excerpts were inspected, not every incoming archive in full.
