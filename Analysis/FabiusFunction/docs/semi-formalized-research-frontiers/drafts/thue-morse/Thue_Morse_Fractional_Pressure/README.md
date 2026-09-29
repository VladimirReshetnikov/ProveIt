# Fractional Cusps at the Atomic Phase

**Sharp noninteger regularity of Thue–Morse pressure and sharp relaxation for digital products in every base**

Research draft prepared with ChatGPT for Vladimir Reshetnikov, 29 September 2026.

## Main result

For the doubling map and `psi_c(x) = log(cos(pi*(x-c))^2)`, write
`p_q(c) = P(q*psi_c)` using natural logarithms. For every `q > 1/2`, the article proves

```text
p_q(c) = 2q log(cos(pi*c))
       + 2(2^(2q)-1) zeta(2q) |c|^(2q)
       + o(|c|^(2q+1)).
```

For noninteger `q > 1/2`, the pressure is locally `C^(ceil(2q)-1)` but has no derivative of order `ceil(2q)` at zero. For integer `q=m`, it is locally analytic and the coefficient of `c^(2m)` vanishes. The binary integer cancellation is credited to the repository predecessor rather than claimed again as new.

The article establishes a general-base normal form, with coefficient `2(b^s-1) zeta(s)` for the absolute-moment exponent `s>1`. It also proves a sharp two-sided operator-norm relaxation estimate on every Hölder space `C^alpha`, `0<alpha<=1`, including the necessary factor `n+1` at `s=1+alpha`.

## Package

- `article.pdf`: the 18-page article.
- `article.tex`: complete editable LaTeX source, including references.
- `code/verify.py`: symbolic checks, high-precision identity checks, and floating-point collocation diagnostics.
- `results/verification.json`: recorded output of the default verification run.
- `results/build_validation.json`: build and rendering receipt.
- `CLAIMS_AND_VALIDATION.md`: scope, dependencies, and verification boundaries.
- `source_manifest.json`: repository snapshot and primary-source ledger.
- `requirements.txt`: pinned versions used for the Python checks.
- `Makefile`: build, verification, and cleanup commands.

## Build

Use a TeX installation containing pdfLaTeX, Libertinus, AMS packages, microtype, booktabs, aliascnt, cleveref, xurl, and the other packages named in the preamble. No custom font files are distributed.

```sh
make pdf
```

Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times. All references are included in the source; no BibTeX run is required.

## Reproduce the checks

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The default grid has at least 65,536 points, rounded up to a multiple of the base; two additional diagnostics use a doubled grid. To perform only the symbolic and high-precision identity checks:

```sh
python code/verify.py --skip-numerics --output results/identities_only.json
```

To use a larger grid without overwriting the delivered receipt:

```sh
python code/verify.py --grid 131072 --output results/refined.json
```

`make clean` removes TeX intermediates without removing the PDF or verification output.

## Scope and status

The central theorems have detailed written proofs. They have not been independently refereed, verified in Lean or Rocq, or certified by interval arithmetic. Numerical residuals are diagnostics, not rigorous error bounds. No unrestricted priority claim is made.

The regularity classification is local at the atomic phase and concerns `q>1/2`. The article does not settle phase regularity at arbitrary nonzero phases or at and below the critical order. Nine further research questions address these boundaries, finer expansions, full spectra, other masks, and formalization.

The source repository was inspected at commit `afb2d1227d8bc5df3beffc1463e958db3544960b`. Nothing in the repository was changed.
