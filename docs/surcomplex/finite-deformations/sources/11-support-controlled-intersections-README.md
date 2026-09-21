# Finite Intersections in Surcomplex Analysis

**Support-Controlled Division, Residue Duality, and Sharp Root Stability**  
Research manuscript, September 21, 2026. The supplied PDF has 30 pages.

## Contents

- `surcomplex_intersections.pdf`: complete article, including proofs, examples,
  scope and priority discussion, and references.
- `surcomplex_intersections.tex`: self-contained LaTeX source; references are
  embedded, so no separate bibliography file is needed.
- `verify_examples.py`: exact symbolic consistency checks using SymPy.
- `verification_report.txt`: the output of the supplied checks (58 passed).
- `requirements.txt`: dependency for the verification script.
- `build.sh` / `build.ps1`: PDF build scripts for Unix-like systems / PowerShell.

## The mathematical contribution

The principal hypothesis is explicit: on a fixed ordinary polydisk, the system
is `F_i(s,z) = z_i^(d_i) + E_i(s,z)`, where each perturbation is a Hahn family of
ordinary holomorphic coefficient functions with well-ordered positive support.
Supports may be infinite, the value group may have arbitrary rank, and the
variables may be coupled. The article proves:

1. Fixed-domain division, a finite free parameter algebra of rank `prod(d_i)`,
   and an explicit contraction of the perturbed Koszul complex (Sections 3-4).
2. Identification with actual surcomplex zero clusters, including exact local
   intersection multiplicities and finite fibers (Section 5).
3. A multidimensional Hahn contour residue, perfect residue duality,
   a Bezoutian reproducing kernel, and the Jacobian trace formula (Sections 6-8).
4. Valuation stability of the algebraic data and a sharp inverse-Jacobian
   threshold for persistence and displacement of simple roots (Section 9).
5. A coupled two-variable example with collisions, explicit multiplication
   matrices, and cancellation of infinite local residues (Section 10).

The constructions control both well ordering and finite contribution at every
Hahn exponent. They do not infer convergence merely from increasing valuation.

## Scope and priority

The manuscript develops the several-variable direction identified in the
user-supplied `surcomplex_analysis(2).tex`. It is standalone and does not require
that file to compile. The original attachment is not included in this archive.

The support-controlled package is presented as a proposed research extension,
not a priority-certified theorem or a solution of a named published conjecture.
Classical homological perturbation, finite intersection algebras, Grothendieck
residues, and residue/trace identities are explicitly credited. The main theorem
is not asserted for every isolated ordinary complete intersection. Section 13
states the extension criterion and the remaining generality questions.

## Build the PDF

Install a LaTeX distribution that includes pdfLaTeX, Latin Modern, AMS packages,
mathtools, mathrsfs, microtype, booktabs, enumitem, fancyhdr, hyperref and cleveref.
A standard TeX Live or MiKTeX installation with these packages is sufficient.
No private fonts, external figures, network access, shell escape, BibTeX, or
Python are needed for the PDF build.

Unix-like shell:

```sh
./build.sh
```

PowerShell, from this directory:

```powershell
./build.ps1
```

Alternatively, run this command three times:

```text
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_intersections.tex
```

Repeated passes resolve the table of contents, cross-references and citations.

## Reproduce the symbolic checks

Python 3.9 or newer is required. The included report was produced with
Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The script prints its report and overwrites `verification_report.txt` beside
it. Any failed identity raises an exception and terminates the run.

The 58 checks cover the unperturbed Koszul contraction identities, a coupled
truncated division calculation, ideal annihilation and commuting multiplication
matrices, exact relations in the four-point example, the Jacobian discriminant,
residue duality and trace identities, and the exponential-numerator residue
coefficients through degree 12. Division truncations are modulo tau^6. The
script uses `a` for the ordinary parameter called `s` in the article.

These are exact finite consistency checks, not a formal verification of the
infinite-support, local-algebra, or stability proofs. The general proofs and
support audit are in the article.

## Production checks

The PDF was compiled with no remaining LaTeX warnings or unresolved references.
All pages were rendered and inspected; text-boundary checks detected no clipped
spans. These are document-quality checks, not independent mathematical refereeing.
