# Gamma and Zeta over the Surcomplex Numbers

**Canonical finite lifts, infinite Dirichlet series, phase obstructions,
and the Riemann hypothesis**

September 2026. An AI-assisted research study prepared for Vladimir Reshetnikov.

## Read

- `article.pdf`: the 28-page article, with complete arguments for its derived
  theorems, a table of contents, notation index and 23 bibliography entries.
- `article.tex`: the complete standalone LaTeX source; the bibliography is
  internal, so no `.bib` file is needed.
- `code/checks.py`: exact finite symbolic checks, not a surreal arithmetic engine.
- `data/finite-checks.json`: the recorded result of 221 passing checks.
- `data/source-audit.json`: source scope and the pinned repository snapshot.
- `data/proof-status.json`: proof boundaries and unverified external inputs.
- `data/build-quality.json`: PDF build and inspection record.

## Main results

1. Canonical finite Taylor–Laurent lifts preserve the exact zero and pole
   divisors. Their RH is equivalent to ordinary RH.
2. A specified symmetric infinitesimal-perturbation stability property for the
   completed zeta function is equivalent to ordinary RH **and simplicity of
   every nontrivial zero**.
3. At positive infinite real part with finite imaginary part, arbitrary complex
   arithmetic coefficients give a strongly summable, injective realization of
   the Dirichlet-convolution algebra. Zeta has an exact Euler product and no
   zeros on this domain.
4. An infinite-shift Hurwitz expansion satisfies exact shift and differential
   identities; differentiating at parameter zero recovers the Stirling
   log-Gamma.
5. Infinite phase periods obstruct a global Gamma reflection formula with only
   ordinary poles. The phase-forgetting exponential is incompatible with a
   single-pole zeta function obtained by the specified coherent galaxywise
   Dirichlet continuation.
6. Elementary-extension models support actual infinite-height zeros and
   transfer classical estimates, but their transported operations are not
   automatically the canonical surreal operations.
7. Assuming RH and simplicity, nonreal zeros at negative infinitesimal
   de Bruijn–Newman time must have infinite modulus.

The article distinguishes established classical inputs, existing repository
results, new derived formulations and unverified priority claims. Recent
August/September 2026 proportion preprints are clearly marked as external
preprint inputs. No proof of classical RH, globally unique surcomplex zeta
function, or complete Lean formalization is asserted.

## Repository scope

The study inspected the maintained documentation catalogue and the guides to
Gamma functions, surcomplex analysis and trigonometry at repository commit:

`905dd19954db43ac81f76f72036520d0eadc5710`

This is a targeted documentation audit, not an exhaustive proof review of the
repository. The repository was not modified. Existing Gamma nonuniqueness and
finite-phase results are explicitly credited rather than claimed as new.

## Build the PDF

Use a reasonably complete TeX Live or MiKTeX installation with pdfLaTeX.
The source uses standard packages, including AMS mathematics, Latin Modern,
`microtype`, `geometry`, `xcolor`, `booktabs`, `enumitem`, `fancyhdr`,
`xurl`, `hyperref` and `bookmark`. No custom font files or external figures
are required.

```sh
./build.sh
```

The script writes intermediate files into `build/` and copies the resulting
PDF to `article.pdf`. Alternatively, run pdfLaTeX on `article.tex` three times.

## Rerun the finite checks

Tested with Python 3.13.5 and SymPy 1.14.0; Python 3.10 or later is recommended.

```sh
python -m pip install sympy==1.14.0
python code/checks.py
```

By default, the program only prints JSON and does not overwrite the recorded
report. To write a separate rerun record:

```sh
python code/checks.py --output /tmp/surcomplex-checks-rerun.json
```

These checks concern finite polynomial and truncated-series identities.
They do not verify Hahn summability, class-sized quantification, the ordinary
RH, the external proportion preprints, or a global analytic continuation.
