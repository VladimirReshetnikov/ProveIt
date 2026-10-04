# Phase-Accurate Reversion of Complex Transseries

**Minimal action jets, sharp Newton stopping, and sectorial transport**  
Research article prepared for Vladimir Reshetnikov, 4 October 2026.

## Read

`article.pdf` is the 29-page article. `article.tex` is its self-contained LaTeX source.

The main results concern the precision required when an approximate inverse is substituted into an exponential phase. For the nonlinear core `F(z)=z+a*z^beta`, the article proves an exact minimal positive-power phase jet, the exact leading Newton error, and the sharp fixed-step threshold `(2^(k+1)-1)*(1-beta) > sigma` for a transported power phase. It separately proves moving Newton-count laws for resolving an exponentially small inverse correction and for evaluating a higher-height phase. An explicit height-two example has no finite expanded phase jet; a Lambert-W cutoff gives a sufficient moving truncation.

General tools include a holomorphic residual-to-phase certificate and an analytic mixed-sector inverse formula with an explicit tail. The article also treats critical amplitude-normalization bias, curved decay boundaries, and two countable-action obstructions, and proposes nine further research projects.

## Mathematical status

The article contains conventional mathematical proofs. It does not claim an unrestricted compositional field or summability theorem for all complex transseries, a solution of a named community-wide open conjecture, independently established publication priority, or Lean verification.

Classical Lagrange inversion, established resurgent closure, the repository's existing Newton depth, and prior nonlinear Stokes transport are credited explicitly. The proposed contributions are the precise refinements and scoped obstruction theorems developed in the article. The repository audit was bounded, not exhaustive.

Numerical tests are high-precision diagnostics, **not directed-rounding interval certificates**. The analytic estimates are proved in the manuscript rather than inferred from sampling.

## Files

- `article.tex`, `article.pdf`: editable source and rendered article.
- `verify.py`, `requirements.txt`: exact rational/symbolic checks and high-precision diagnostics.
- `results/verification.json`, `results/verification.txt`: recorded executed results and a readable summary.
- `build.sh`: PDF build; auxiliary files go into `build/`.
- `SOURCES.md`, `QA_REPORT.md`, `SHA256SUMS.txt`: provenance, quality checks, and checksums.

## Reproduce

Python 3.10 or newer is recommended. The recorded run used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. Install the pinned Python dependencies and run:

```sh
python -m pip install -r requirements.txt
python verify.py --out build/results
sh build.sh
```

`verify.py` defaults to `build/results` and never uses the network or external datasets. The `--part exact` and `--part numerical` options run the two suites separately. The recorded `results/verification.json` is not overwritten by the default command.

The PDF requires pdfLaTeX and the standard packages listed in the preamble, available in a suitable TeX Live installation. `build.sh` runs three passes and copies the final PDF to `article.pdf`. On a system without a POSIX shell, run pdfLaTeX three times manually on `article.tex`.

All 710 exact assertions passed. Numerical diagnostics used 160 decimal digits. The final PDF compiled with no warnings, undefined references, overfull boxes, or underfull boxes. All pages were rendered and inspected for layout.

No external repository was modified. No third-party source corpus, font files, or external figures are included.
