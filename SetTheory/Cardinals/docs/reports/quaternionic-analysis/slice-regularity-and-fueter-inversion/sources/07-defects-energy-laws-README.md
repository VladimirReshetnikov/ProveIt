# Global Fueter Primitives
## Period Obstructions, Spherical Defects, and Sharp Energy Laws

Research article prepared on 21 September 2026 as an extension of the supplied
quaternionic-analysis manuscript. The main files are:

- `global_fueter_primitives.pdf`: the complete typeset article.
- `global_fueter_primitives.tex`: self-contained LaTeX source, including bibliography.
- `source_context/quaternionic_analysis(1).tex`: the user's original manuscript,
  copied unchanged for context.
- `literature_log.md`: searched directions, source scope, and novelty qualifications.
- `checks/verify.py` and `checks/verification_results.json`: symbolic identities,
  period tests, sharp logarithmic energy, and renormalized-energy diagnostics.
- `checks/verify_sources_and_poles.py` and `checks/source_and_pole_results.json`:
  independent quaternionic Cauchy-layer integration and higher-pole energy tests.
- `requirements.txt`, `build.sh`, and `build.ps1`: reproduction helpers.

## Main results

The convention is left slice regularity with right quaternionic coefficients;
Cauchy–Fueter regularity uses D = partial_x + i partial_1 + j partial_2 + k partial_3.
The Fueter map is the ordinary four-dimensional Laplacian.

1. Two closed quaternion-valued forms computed directly from an axial Fueter field
   give necessary and sufficient conditions for a global slice-regular primitive.
   Their periods describe the complete affine monodromy.
2. On the explicitly stated finite-type symmetric planar domains, each conjugate
   pair of holes contributes exactly two quaternionic obstruction parameters.
   Reflection-fixed holes contribute none. The cokernel therefore has quaternionic
   dimension 2h, or real dimension 8h. Explicit spherical kernels split the period map.
3. The range is closed, and rational approximation becomes possible after adding
   precisely the necessary fixed period defects.
4. Every finite-order spherical singularity has a unique decomposition into a
   period defect, finitely many rational Fueter principal parts, and a removable field.
5. For a sphere s+t*S and critical growth O(1/rho), the squared L2 norm diverges as
   8*(t^2*|a|^2 + |s*a+b|^2)*log(R/epsilon) plus a finite renormalized limit.
   A matching sharp leading lower bound requires no pointwise growth hypothesis.
6. The period defect has an explicitly normalized surface source, a Cauchy-layer
   representation, and an associated sharp L2 removability threshold.

The energy here is the L2 norm squared of the field, not the energy of its gradient.
All outer energy radii are strictly inside the neighborhood of regularity.

## Mathematical status

The article supplies analytic proofs of its main assertions. It uses established
complex analysis and elliptic facts, including Runge approximation, Laurent theory,
Weyl's lemma, and Liouville's theorem, as clearly identified inputs. It is not a
Lean or other proof-assistant formalization. Numerical tests are diagnostics, not
certified bounds or substitutes for proofs.

Local inverse Fueter theory and spherical Cauchy kernels are known results and
are explicitly attributed. The proposed contributions are the reflection-sensitive
range classification, period-normalized finite-growth normal form and approximation
consequences, and sharp energy/source formulas in these coordinates. A targeted
literature search did not locate these exact statements; this does not establish
exhaustive priority. No named published conjecture is asserted to be settled.

## Build the article

Install a LaTeX distribution with pdfLaTeX and the packages used in the preamble,
including newtx, amsmath, amsthm, mathtools, geometry, microtype, enumitem, fancyhdr,
hyperref, bookmark, booktabs, and tabularx.

On a POSIX shell:

    ./build.sh

On PowerShell:

    ./build.ps1

Or run twice from this directory:

    pdflatex -interaction=nonstopmode -halt-on-error global_fueter_primitives.tex
    pdflatex -interaction=nonstopmode -halt-on-error global_fueter_primitives.tex

The bibliography is embedded; BibTeX is not needed. The supplied PDF is already built.

## Reproduce the diagnostics

Use Python 3.9 or later and install the dependencies:

    python -m pip install -r requirements.txt
    python checks/verify.py --output checks/verification_results.json
    python checks/verify_sources_and_poles.py --output checks/source_and_pole_results.json

The archived run used NumPy 2.3.5, SymPy 1.14.0, and SciPy 1.17.0.
Floating-point last digits and quadrature estimates can vary across environments.
All seven symbolic tests passed. Period errors were below 1.05e-14, the Cauchy-layer
comparison error was below 2.01e-15, and the energy diagnostics approached the
proved constants. Read the JSON files for exact sample data and outputs.
