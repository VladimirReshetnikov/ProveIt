# Periods, Global Fueter Primitives, and Integrable Spherical Singularities

Research manuscript, 21 September 2026.

## Contents

- `quaternionic_periods.pdf`: the 21-page article, with complete proofs and linked references.
- `quaternionic_periods.tex`: self-contained LaTeX source; no external bibliography or figures are required.
- `verify.py`: deterministic symbolic identities and numerical consistency checks.
- `verification_results.json` and `verification_results.txt`: recorded results of the checks.
- `build.ps1` and `build.sh`: optional PDF build scripts for PowerShell and POSIX shells.

## Results and locations

**Theorem 3.2** gives a necessary and sufficient global inverse-Fueter criterion on any connected upper-half-plane meridian. Two closed quaternion-valued one-forms, defined directly from the target function, give every obstruction. Their periods are exactly the two coefficients of affine monodromy.

**Theorem 4.2** realizes every obstruction for a finitely connected meridian and gives an explicit split exact sequence. With m holes, the cokernel has quaternionic dimension 2m (real dimension 8m).

**Theorems 5.1 and 5.2** treat domains meeting the real axis. Reflection-invariant cohomology is the relevant obstruction space: conjugation-fixed holes contribute none, while each exchanged pair contributes two quaternionic coordinates.

**Theorem 6.3** proves a period-corrected Runge approximation theorem. Proposition 6.1 gives quantitative lower bounds showing why the correction cannot be omitted for nonzero periods.

**Theorem 8.1** classifies every locally L1 axial Fueter-regular singularity along a nonreal conjugacy sphere, modulo a removable function, by two quaternionic residues. Proposition 8.3 shows that below L1, zero residues need not imply removability.

**Theorems 9.2 and 9.4** identify the exact logarithmic L2-energy coefficient and the affine-density Dirac source on the sphere. The logarithm-subtracted energy has a finite limit. Corollary 9.3 proves that L2 is a sharp removability threshold within the stated class. Corollary 9.7 recovers both residues from two conserved three-dimensional boundary fluxes; one ordinary flux alone is insufficient.

## Scope and novelty

All results concern one quaternionic variable, left Fueter regularity, and right quaternionic coefficients. The singularity classification is for axial functions and complete nonreal conjugacy spheres. It is not a theorem for arbitrary nonaxial singularities or arbitrary singular sets.

The local inverse Fueter theorem, affine kernel, and underlying spherical/arctangent kernels are established literature and are credited explicitly. The proposed contributions are the exact global period/splitting formulations and the integrable residue–defect–flux–energy classification. A targeted literature review did not locate these combined statements in the inspected primary sources. This is not a certification of priority or a claim to solve a named published conjecture. Section 11 records the comparison and limitations.

## Building the PDF

Use a TeX installation with pdfLaTeX and the packages named in the preamble, including `newtxtext`, `newtxmath`, `amsmath`, `amsthm`, `mathtools`, `geometry`, `microtype`, `booktabs`, `tabularx`, `xcolor`, `enumitem`, `fancyhdr`, `etoolbox`, `needspace`, `hyperref`, and `bookmark`.

From the extracted directory, run `./build.sh` in a POSIX shell or `./build.ps1` in PowerShell. Alternatively, run the following command three times:

```text
pdflatex -interaction=nonstopmode -halt-on-error quaternionic_periods.tex
```

Multiple passes resolve the table of contents, theorem references, and bibliography. The included PDF was built successfully with pdfTeX 1.40.26; its final log had no warnings or overfull boxes. All pages were rendered, and text bounding boxes were checked for clipping.

## Running the computational checks

The script uses Python 3.10+ with NumPy and SymPy. The recorded run used NumPy 2.3.5 and SymPy 1.14.0. Run:

```text
python verify.py
```

It overwrites the two result files beside the script and raises an exception if a check fails. Its 13 exact symbolic checks passed. Numerical tests checked period normalization, both conserved fluxes on several tubes, and convergence to the predicted energy coefficient for non-real quaternionic residues.

The largest recorded period error was about 1.11e-16; the largest conserved-flux component error was about 2.01e-12. These are floating-point consistency checks, not certified quadrature error bounds. No formal proof assistant was used. The analytical and topological proofs are in the article and do not depend on numerical evidence.
