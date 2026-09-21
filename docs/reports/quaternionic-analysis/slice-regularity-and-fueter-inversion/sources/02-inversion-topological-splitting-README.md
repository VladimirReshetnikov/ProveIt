# Global Fueter Inversion
## Period obstructions, topological splitting, and spherical singularities

Research article dated 21 September 2026. The compiled article has 21 pages.

## Files

- `global_fueter_inversion.pdf`: complete article, with proofs and references.
- `global_fueter_inversion.tex`: self-contained LaTeX source; bibliography is embedded.
- `verify_results.py`: reproducible symbolic and numerical formula audits.
- `verification_results.json`: actual results from the included script.
- `requirements.txt`: exact versions of the Python packages used for these audits.
- `build.sh`: three-pass PDF build script.

## Main results

The article constructs two explicit closed quaternion-valued one-forms whose
periods are necessary and sufficient for a global slice-regular Fueter inverse.
It computes and splits the obstruction space on the stated finite-hole domains.
Only conjugation-exchanged hole pairs contribute on domains meeting the real
axis. It then classifies finite-growth singularities along a nonreal sphere:
the singular quotient at growth O(rho^(-N)) has real dimension 8N. At critical
order, the periods are the coefficients of an affine spherical source density.
The article also proves the exact logarithmic energy coefficient, sharp
subcritical growth and L2 removability, quantitative separation estimates,
and approximation with the minimal finite-dimensional obstruction space.

## Relation to the supplied source and to published work

This is a standalone companion to `quaternionic_analysis.tex`, rather than an
edited copy of that exposition. It develops the topology question following the
source's constructive local inverse theorem. The supplied file is not needed
to compile or understand the proofs and is not duplicated in this archive.

Local inverse Fueter theory and the arctangent/logarithmic kernels are known
results and are credited accordingly. The proposed contributions are the
complete explicit obstruction, splitting, and spherical singularity package.
The article distinguishes these candidate-original formulations from known
results. The targeted literature search did not establish an earlier identical
complete formulation, but this is not a guarantee of priority. The manuscript
has not been peer reviewed or formally verified.

## Rebuild the PDF

Use a LaTeX installation containing the packages listed at the start of the TeX
file, including `newtxtext` and `newtxmath`. On a Unix-like system run:

```sh
sh build.sh
```

Alternatively, run the following command three times from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error global_fueter_inversion.tex
```

No bibliography processor, image assets, or internet access is needed to compile.
The delivered PDF compiled without undefined-reference or overfull-box warnings.

## Reproduce the formula audits

```sh
python -m pip install -r requirements.txt
python verify_results.py --output verification_results.json
```

The delivered report records Python 3.13.5, SymPy 1.14.0, and
mpmath 1.3.0. All 31 symbolic and 16
numerical checks passed. The numerical work uses 50 decimal digits.

The audits cover the kernel formulas, Vekua equations, primitive forms,
holomorphic detector, quaternionic charge moments, energy quadratic form,
period normalizations, and convergence of normal-circle flux and energy slopes.
They are checks of formulas, not proofs of topology, global solvability,
removability, or originality. The analytic proofs are in the article.

## Important scope restrictions

The singularity classification concerns axial monogenic functions near a full
nonreal sphere of positive radius. It does not classify arbitrary nonaxial
Fueter-regular fields or singularities at real points. Finite-dimensional kernel
splitting is proved for the explicit finite-hole domain class in Section 4;
the zero-period inverse criterion itself applies to arbitrary connected bases
of the two types defined in Section 2.
