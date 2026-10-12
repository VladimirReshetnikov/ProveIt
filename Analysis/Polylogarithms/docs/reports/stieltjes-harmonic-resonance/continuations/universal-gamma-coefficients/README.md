# Universal Gamma Normal Forms

**Rational Kernels, Harmonic Sums, and Stieltjes Primitives**  
Research continuation prepared with ChatGPT for Vladimir Reshetnikov.  
Research date: 11 October 2026.

## Read the article

`Universal_Gamma_Normal_Forms.pdf` is the compiled 28-page article.
`Universal_Gamma_Normal_Forms.tex` is a self-contained single-file source.
`article.tex`, `sections/`, and `references.tex` are the modular sources.

The main theorem gives **every coefficient of every canonical inverse-Gamma
Bell polynomial**, not just the first four derivative variables. The proof uses
an all-order telescoping rational-kernel identity. It determines the exact
support and the sign of each nonzero canonical coefficient. It also supplies
ordinary entire integral generators for every finite derivative projection.

The complete mixed `u0,u1,u2,u3` formulas and the closed all-order numerator
polynomials resolve questions 5 and 6 of the inspected predecessor's research
section. The universal result extends these answers to arbitrary highest
positive derivative index.

Applications include finite polylogarithmic lifts, generalized harmonic sums,
arithmetic-step digamma sums and Gamma-product primitives, balanced
Hurwitz–Stieltjes identities, and weighted Gamma/Stieltjes primitives with their
full total-derivative compensators.

## Reproduce the checks

Use Python 3.10 or later and install `requirements.txt`. From this directory:

```sh
python code/check_universal.py
python code/check_exact.py
python code/check_applications.py
python code/check_numeric.py
python build.py
```

The scripts require no network access or repository checkout. Building the PDF
requires pdfLaTeX and the packages listed in the preamble. `build.py` assembles
the single-file TeX source and runs three LaTeX passes.

Recorded results in `data/`:

- 28,629 exact comparisons of the universal beta formula with an independent
  Fraction normalizer through weight 30, including all predicted zeros.
- 2,724 overlapping four-variable coefficient checks, 31 full polynomial
  decomposition checks, and 18 symbolic rational-function recurrence checks.
- Exact harmonic endpoints, arithmetic-step values, support counts, and
  truncation/sign corruption controls.
- 65 floating-point diagnostics at 60 decimal working digits. These are not
  interval certificates and are not the proof of the infinite-family theorems.

`data/normal_forms_through_18.json` contains the complete Bell polynomials,
normal forms, and exact total-derivative polynomials through weight 18. Each
entry is a rational coefficient string and a finite exponent vector.

## Provenance and scope

The pinned comparison revision is
`af91e74dfa841331c51e867542345a3643ee0bf0`.
The two primary source blobs and the manuscript README blob are listed in
`data/provenance.json`. Incoming archive metadata was inspected; archive members
were not retrieved. This is a targeted comparison, not an exhaustive audit of
all incoming packages or a proof of historical priority.

The normal-form convention and finite-jet principle are inherited and cited.
The main all-order rational-kernel proof, complete coefficient formula, and
support/sign theorem are the structural advance relative to the inspected
research targets. Classical Gamma/Hurwitz identities and elementary partial
fractions are not claimed as new.

The general unequal-tail optimal-prefix conjecture and the Gaussian S6/current
S8 period conjectures are not resolved by this package. No arithmetic
independence or proof-assistant formalization is claimed.

See `INTEGRATION_NOTES.md` for suggested repository placement and status changes.
No remote repository files have been modified. `MANIFEST.sha256` records the
SHA-256 digest of every deliverable file except itself.
