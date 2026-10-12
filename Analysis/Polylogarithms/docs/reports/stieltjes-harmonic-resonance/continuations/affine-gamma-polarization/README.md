# Affine Polarization of Gamma Normal Forms

Research continuation prepared for Vladimir Reshetnikov and ProveIt, 11 October 2026.

## Principal results

The article proves an all-order formula for the coefficient of `u0^a u1^k ur^2`
in the canonical integration-by-parts normal form of the inverse-Gamma hierarchy,
for every `r >= 2` and every `a,k >= 0`. An affine perturbation gives the entire
kernel

`g_r(y) = (-1)^r/(r+1)! * (d/d(y^2))^(r+1) cosh(y)`.

Its beta representation produces finite Hurwitz and Lerch endpoint formulas,
all generalized Stieltjes orders, and fully anchored shift primitives. A
Bernoulli-polynomial basis is characterized by single-zeta closure **as a
meromorphic-function identity over C(s)**. This is not an assertion of
independence of numerical zeta values. Explicit consequences include six
quartic-weight polygamma integrals, one first-Stieltjes integral, an ordinary
three-polylogarithm integral, and a family selecting one odd zeta value.

The article contains full proofs and ten further research questions.

## What is and is not claimed

The normal-form decomposition, pure derivative-square coefficients, and the
complete `r = 2` coefficient family are inherited and credited. The new
all-derivative formula resolves the no-additional-`u2` part of the predecessor's
next-Gamma-projection question. The full mixed `u2,u3` projection, general
unequal-tail optimal-prefix conjecture, Gaussian S6, and revised S8 remain open.

The work has mathematical proofs, finite exact checks, and floating-point
diagnostics. It is not proof-assistant formalized, independently peer reviewed,
or a certified interval calculation. Historical priority beyond the inspected
sources is not asserted. No remote repository files were modified.

The source audit is deliberately scoped. Relevant repository TeX was read.
The five current incoming ZIPs were inventoried but not extracted. Matching-title
Library abstracts for three reports were inspected without establishing their
byte identity with the ZIPs. See `SOURCE_AUDIT.md` and the source manifest.

## Contents

- `article.pdf`: typeset research article.
- `article.tex`, `sections/`, `references.tex`: authoritative modular source.
- `standalone.tex`: the complete article in one independently compilable file.
- `verification/`: exact algebra, profile, endpoint, selector, and numerical replays.
- `data/`: exact normal forms with primitives, coefficient tables, and recorded checks.
- `integration/`: additive manuscript fragment, proof-status claims, and integration notes.
- `tools/`: standalone-source and clean-package builders.
- `SHA256SUMS`: checksums of the packaged files, except the checksum file itself.

## Build

The PDF was built with pdfTeX 1.40.26 from TeX Live 2025/dev/Debian and latexmk 4.86. It uses
standard LaTeX packages, including amsmath, amsthm, mathtools, lmodern,
microtype, hyperref, and bookmark. No bibliography processor, shell escape,
network request, or external image is needed.

```sh
make pdf
make standalone
```

Alternatively:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python3 tools/make_standalone.py
```

`article.tex` is the editing authority. Regenerate `standalone.tex` after editing
any input section. The standalone file can be compiled independently by pdflatex.

## Replay

The recorded environment is Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
The code requires Python 3.10 or later. Install the pinned dependencies, then run:

```sh
python3 -m pip install -r requirements.txt
make verify
```

The replay contains **2,187 exact assertions and 56 numerical comparisons**.
Do not use `python -O`: it disables assertions. The individual scripts can also
run separately. Numerical parts are selected by

```sh
python3 verification/check_numeric.py --part kernel
python3 verification/check_numeric.py --part transform
python3 verification/check_numeric.py --part stieltjes
python3 verification/check_numeric.py --part extras
```

The complete replay takes longer than any one part. `run_all.py --summarize-only`
only aggregates existing JSON results; it does **not** execute checks and should
not be confused with a fresh verification. See `VERIFICATION.md` for tolerances,
independence of constructions, and the limits of finite checks.

## Integration

Suggested additive destination:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/affine-gamma-polarization/`

Read `integration/INTEGRATION.md` before incorporating individual statements.
Preserve the canonical normal-form convention, Stieltjes Laurent sign,
Pochhammer normalization, ordinary-versus-finite-part distinction, and all
anchor conditions.
