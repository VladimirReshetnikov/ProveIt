# Finite Maps and Residue Duality in Hahn-Coherent Surcomplex Analysis

Research article dated September 21, 2026. The PDF has 27 pages.

## Files

- `surcomplex_finite_maps.tex`: complete, self-contained LaTeX source.
- `surcomplex_finite_maps.pdf`: compiled article, with linked contents and references.
- `verify_examples.py`: exact symbolic checks for the worked examples.
- `verification_report.txt`: output from the included script; 25 checks passed.
- `requirements.txt`: tested SymPy version for the verification script.
- `README.md`: this file.

## Mathematical scope

The article develops fixed-domain, support-controlled finite-mapping results for
positive Hahn-coherent perturbations of isolated ordinary complete intersections.
It proves finite freeness of the normalized zero algebra over the Hahn valuation
ring, exact correspondence with surcomplex roots and their local multiplicities,
parameter preparation and division, explicit finite holomorphic families, and
integral residue duality with a trace--Jacobian formula.

The two main examples are a coupled rank-four polynomial family, including
higher-rank scales and residue cancellation, and a genuinely nonpolynomial
multiplicity-five complete intersection.

The homological perturbation lemma, ordinary complete-intersection theory,
and classical local residue theory are established inputs, explicitly cited.
The proposed contributions are their precise arbitrary-support, fixed-domain
Hahn implementations and the pointwise/residue comparisons. A targeted literature
search did not locate the exact package of statements; priority is not certified.
The general theorems have mathematical proofs, not proof-assistant verification.
The symbolic tests check only the stated finite identities and finite series terms.

## Build the PDF

Use a standard TeX Live or MiKTeX installation with the packages named in the
preamble. No external graphics, BibTeX, shell escape, or custom fonts are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_finite_maps.tex
```

Alternatively, run `pdflatex` on the source three times to settle cross-references
and the table of contents.

The supplied PDF was built with pdfTeX 1.40.26. Its final LaTeX log had no
undefined-reference, missing-glyph, overfull-box, or underfull-box warnings.
Rendered pages were inspected and page text was checked for unsafe bounding boxes.

## Run the symbolic verification

Python 3.9 or later is sufficient for the script. Tested here with Python 3.13.5
and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The script writes `verification_report.txt` beside itself and exits with an
exception if any asserted identity fails. It uses exact symbolic arithmetic;
there are no numerical-tolerance checks or external service calls.

## Supplied source and provenance

The requested starting framework was the uploaded manuscript:

`surcomplex_analysis(2).tex`

Title: *Surcomplex Analysis: Infinitesimal Calculus, Hahn-Coherent Holomorphy,
and Contour Theory*.

Original byte size: 105194.
SHA-256: `e6e2ef4a8b8d920fffa7256490f98aa312023078fec966c33b3f204cb17748f4`.

The new paper cites this manuscript as reference [1] and distinguishes its
existing one-variable results from the several-variable extensions developed
here. The original manuscript is not duplicated in this archive.
