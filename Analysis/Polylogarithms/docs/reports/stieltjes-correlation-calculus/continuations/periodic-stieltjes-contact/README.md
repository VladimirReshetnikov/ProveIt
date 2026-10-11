# Periodic Stieltjes Contact Calculus

**All-Index Collision Corrections, Harmonic Derivative Anomalies, and Exact Zeta-Jet Integrals**  
ProveIt continuation, 10 October 2026. Prepared with ChatGPT.

## Main result

This package answers the specific further-research question “The remaining distributional collision law” in the inspected *Coincident-Point Stieltjes Calculus* manuscript. With the original variable and shift variable both using unit-coordinate Hadamard finite parts, the periodic convolution of the individually extended Stieltjes factors differs from the finite-part extension of their off-collision correlation by exactly one delta derivative of order p+q. Its coefficient has an explicit all-index gamma–harmonic generating formula. There are no lower contacts in this convention.

The paper also proves the finite harmonic anomaly of periodic differentiation, a polygamma contact formula, a first-row parity law, stabilization in the derivative split, convergent trigonometric-weighted identities, all positive-integer resonances of a weighted Hurwitz kernel, and normalized polylogarithmic/Bernoulli primitive formulas.

## Contents

- `article.pdf`: compiled article, including proofs and further research questions.
- `article.tex`: main LaTeX source; it inputs `data/validation_summary.tex`.
- `code/exact_engine.py`: exact symbolic replay and contact-coefficient generator.
- `code/verify_numerically.py`: independent coordinate finite-part quadrature and ordinary integral diagnostics.
- `code/build.py`: isolated PDF build with a build receipt.
- `data/contact_coefficients.json`: 441 exact coefficients, with symbolic strings and LaTeX.
- `data/exact_checks.json`: 940 passing exact checks.
- `data/numerical_checks.json`: 69 passing high-precision diagnostics, including individual values and tolerances.
- `data/validation_summary.tex`: recorded computational summary used in the article.
- `data/build_receipt.json`: build result and source/PDF hashes.
- `data/visual_review.json`: PDF rendering and layout checks.
- `integration/INTEGRATION_NOTES.md`: proposed placement and editorial changes.
- `integration/SOURCE_AUDIT.md`: source scope, identities, attribution, and limitations.
- `integration/RESULTS.json`: machine-readable theorem map.
- `MANIFEST.sha256`: hashes of the delivered files, excluding the manifest itself.

## Reproduce

Use Python 3.10 or later and a TeX distribution with `pdflatex`, Latin Modern, the AMS packages, `microtype`, `booktabs`, `enumitem`, `fancyhdr`, `xurl`, `hyperref`, and `bookmark`.

```sh
python -m pip install -r requirements.txt
python code/exact_engine.py
python code/verify_numerically.py
python code/build.py
```

The recorded run used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. The numerical script accepts `--dps` and `--terms`; changing precision alone does not automatically change the fixed local integration truncation. The delivered settings are the tested reference settings. The build script runs three LaTeX passes in a temporary directory and copies only the PDF and build receipt into the package. PDF metadata may change on rebuilding. The validation-summary TeX is a record of the delivered run; reconcile it manually after changing the test scope or tolerances.

To verify delivered hashes on a system with GNU coreutils:

```sh
sha256sum -c MANIFEST.sha256
```

## Evidence and scope

The analytic statements have ordinary mathematical proofs. The exact replay is finite symbolic arithmetic, not proof-assistant formalization. Numerical diagnostics are not interval-certified. The largest normalized residual in the delivered run was 4.1761949e-53, with an acceptance tolerance of 2e-38.

No false theorem was identified in the inspected preceding report: its distributional extension problem was explicitly open. The new formulas are extension safeguards, not corrections to a theorem it did not claim. Classical inputs are credited in the article. Global priority for all specializations has not been established, and unrelated fixed-weight S6/S8 questions remain open.

No repository files were modified. This is a new, integration-ready research delivery, not an applied patch.
