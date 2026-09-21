# Global Fueter Primitives and Spherical Singularities
## Period obstructions, reflection symmetry, and a sharp residue–energy law

Research draft, 21 September 2026.

## Contents

- `quaternionic_fueter_periods.pdf`: compiled article with complete proofs.
- `quaternionic_fueter_periods.tex`: self-contained LaTeX source, including references.
- `verify.py`: exact symbolic checks and independent numerical experiments.
- `verification.txt`: actual output from running the verification program.
- `literature_notes.md`: sources, comparison points, search scope, and limitations.
- `requirements.txt`: Python dependencies used for the checks.
- `Makefile`: PDF and verification build targets.
- `source_reference/quaternionic_analysis.tex`: unchanged user-supplied manuscript.

The new article is self-contained and does not input the supplied manuscript.
That manuscript is retained to document the starting point: its Section 13
proves a simply connected inverse Fueter theorem and explicitly leaves global
existence on domains with holes subject to period conditions.

## Mathematical results

For an axial Fueter-regular field g=P+IQ on the circularization of a planar
domain above the real axis, the article constructs two closed quaternionic
one-forms directly from P,Q. Their periods are necessary and sufficient
obstructions to a global slice-regular primitive under the four-dimensional
Laplacian. Explicit logarithmic defect fields realize all period pairs.

The finite-connectivity cokernel has real dimension 8m for m product-domain
holes. For smooth symmetric stems on a domain meeting the real axis, only
conjugate pairs of nonreal holes contribute, giving dimension 8k for k pairs.

Near a removed nonreal conjugacy sphere, the same two quaternionic periods
are residues in a Laurent–logarithmic normal form. At transverse growth
O(1/rho), they classify the entire singularity modulo smooth extensions.
They force a sharp logarithmic lower bound on four-dimensional energy,
and determine its exact coefficient and a finite renormalized remainder
at critical growth. A separate proof establishes sharp local L2 removability.

All operators, domain assumptions, signs, and normalizations are specified in
the article. Inversion of arbitrary nonaxial Fueter-regular fields is not claimed.

## Evidentiary and novelty status

This is an original research draft, not a peer-reviewed paper or a
proof-assistant certificate. The mathematical arguments are provided in full.
The exact global obstruction/residue–energy package was not found in the
bounded literature review described in the article and `literature_notes.md`.
This is not certification of publication priority. Local inverse Fueter theory,
the affine kernel, and general elliptic removability techniques are explicitly
credited as established material. No named longstanding conjecture is claimed
solved.

The program checks formulas and selected numerical examples. It does not
replace the proofs and cannot establish novelty.

## Build the PDF

A TeX Live installation with `newtx`, `amsmath`, `amsthm`, `mathtools`,
`geometry`, `microtype`, `booktabs`, `tabularx`, `xcolor`, `enumitem`,
`etoolbox`, `fancyhdr`, `hyperref`, and `bookmark` is sufficient.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error quaternionic_fueter_periods.tex
```

Alternatively, run `pdflatex` at least twice, until references stabilize.
The bibliography is embedded; no BibTeX or external image files are required.

## Reproduce the computational checks

Python 3.10 or later is required. The supplied output was produced with
Python 3.13.5, SymPy 1.14.0, and NumPy 2.3.5.

```sh
python -m pip install -r requirements.txt
python verify.py > verification.txt
```

The script checks the two Vekua equations, the holomorphic invariant, the
primitive identities, several independent polynomial/rational examples,
both period families, zero winding, a two-hole correction, and the energy law.
The coefficient test uses non-collinear quaternionic coefficients and has
predicted logarithmic coefficient 252. The smallest tested decade annulus
gives 252.000000155005; changing quadrature resolution changes that value by
less than 3e-14 in the recorded run.

The numerical routines use deterministic trapezoidal circle quadrature and
Gauss–Legendre integration in log radius. No random seed or external service
is needed. See the code and output for tolerances.
