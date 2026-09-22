# Surreal and Surcomplex Numbers in Theoretical Physics

## Article

**Asymptotic structure, black-hole singularities, and the limits of replacing the scalar field**

Prepared for Vladimir Reshetnikov, September 21, 2026.
The PDF has 29 pages, including the title page, contents, two appendices, and 18 references.

The main conclusion is that surreal and surcomplex numbers have substantial potential as an exact language for controlled asymptotic and formal field theories. Merely extending the scalar field does not remove a black-hole singularity, define division by zero, determine ultraviolet dynamics, or supply an observable rule.

The article distinguishes algebraic scalar extension, non-Archimedean coefficient fields on ordinary spacetime, and a genuinely surreal-valued spacetime. It contains explicit Schwarzschild infall and tidal calculations, conditional standard-part reduction theorems for Einstein equations and finite quantum protocols, a regular-core comparison, transseries and renormalization examples, and a staged development program for the supplied repository.

## Contents of this package

- `surreal_numbers_black_holes.tex`: standalone LaTeX source, with embedded bibliography.
- `surreal_numbers_black_holes.pdf`: compiled article.
- `verify_identities.py`: exact symbolic checks for the worked examples.
- `verification_results.txt`: recorded output, with all 50 checks passing.
- `requirements.txt`: tested SymPy version for the optional checks.
- `build.sh` and `build.ps1`: Linux/macOS and PowerShell build helpers.
- `CHECKSUMS.sha256`: SHA-256 checksums of package files.

## Build the article

A conventional LaTeX installation with pdfLaTeX and latexmk is sufficient. The source uses standard AMS, Latin Modern, geometry, microtype, booktabs, enumitem, fancyhdr, hyperref, bookmark, and related packages. No external graphics, BibTeX database, or Biber run is required.

From the package directory:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_numbers_black_holes.tex
```

Alternatively, run `bash build.sh` or, in PowerShell, `./build.ps1`. The helper scripts place intermediate files under `build/` and copy the resulting PDF to the package directory.

## Run the optional checks

The recorded run used Python 3.13.5 and SymPy 1.14.0. The script uses Python 3.9-or-later syntax.

```text
python -m pip install -r requirements.txt
python verify_identities.py
```

The checks independently construct the static spherical connection and curvature tensor, verify its contraction and Schwarzschild Ricci components, and test the displayed geodesic, tidal, Kasner-coefficient, regular-core, scaling, regulator, Borel-residue, and double-null identities.

These checks are not a formal verification of the general mathematical proofs. They do not establish analytic realization of formal series or physical singularity resolution. No independent Lean build of the repository was performed for this article.

## Repository and source scope

The reviewed repository snapshot is:

```text
VladimirReshetnikov/Surreal
39f2be6667ade51bca2b45daa47e289d69c09764
```

The review inspected the root README, research catalogue, relevant foundations in the surcomplex analysis source, and the trigonometry report's detailed description. The article records the distinction between implemented generic Lean prerequisites and the larger unrefereed manuscript collection. It does not claim to have audited all source reports.

The bibliography supplies pinned repository links and primary research sources. The search was targeted, not an exhaustive survey. The elementary results and conditional theorems are presented without a priority claim. A physical quantum-gravity model resolving black-hole singularities is not claimed.
