# Jordan Separation, Cauchy Theory, and Stokes Calculus on the Surcomplex Plane

Research article dated September 21, 2026.

## Contents

- `surcomplex_contours.pdf`: complete typeset article.
- `surcomplex_contours.tex`: self-contained LaTeX source, including bibliography.
- `verify_examples.py`: exact symbolic checks of the worked examples.
- `verification_output.txt`: recorded successful run (317 exact checks).
- `cross_check.wl`: independent Wolfram Language coefficient cross-check and recorded output.
- `README.md`: this file.

## Scope

The article studies the Jordan curve theorem, Cauchy's integral theorem,
and generalized Stokes in several precisely distinguished settings:
full-class fine topology, a fixed Hahn field's internal topology, the coarse
standard-part topology, semialgebraic/definable topology, and Hahn-coherent
forms and chains. It also compares Berkovich/tropical integration, definable
integration, surreal antiderivative extensions, and roots-of-unity averages.

Detailed proofs are supplied for the coefficientwise de Rham construction,
Stokes on infinitesimally deformed chains, an exact endpoint correction,
positive microscopic rescaling of radius-free analytic germs, and contour
representations of perturbation residues. The general complete-intersection
representation uses the classical residue transformation law and integrates
a transformed differential form with its essential determinant factor.
A rational contour pairing is defined independently using semialgebraic
winding numbers, with a comparison on explicitly admissible overlaps.

Established literature, results reported in the supplied manuscripts, and
extensions proved in this article are distinguished. The supplied manuscripts
are research manuscripts, not treated as independently refereed sources.
No exhaustive priority claim or machine-verified proof of the theorems is made.

## Source relationship

The user's source files are cited as:

- `surcomplex_analysis(3).tex`
- `surcomplex_analytic_geometry.tex`

Those files are not required to compile this article and are not duplicated
in the archive. Published sources have bibliographic entries and links in
the article. The literature search was targeted, not exhaustive.

## Compile

In a LaTeX installation with the standard packages used in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_contours.tex
```

Alternatively, run `pdflatex surcomplex_contours.tex` three times to resolve
the table of contents and cross-references. No BibTeX, external graphics,
nonstandard font files, or shell-escape setting is required.

## Run the example checks

With Python 3 and SymPy installed:

```sh
python verify_examples.py
```

To replace the recorded output with a fresh run:

```sh
python verify_examples.py > verification_output.txt
```

The script checks exact expressions, Taylor coefficients, matrix identities,
residue traces, and finite roots-of-unity character averages. It does not
implement arbitrary ordered groups or Hahn fields. A passed finite check is
not proof of an infinite-support or general topological statement.

The included run used the Python and SymPy versions listed at the top of
`verification_output.txt`. The Wolfram file can be run separately in a
Wolfram Language kernel; its recorded list was independently evaluated.

## Mathematical cautions

An ordinary real-parameter contour in these constructions is not claimed to
be a nonconstant fine-continuous path. Definably connected components are not
ordinary topological connected components. Hahn strong summation is not a
valuation limit or a full-fine-topology limit. Semialgebraic and tropical
integration may have different target spaces from the Hahn-valued functional.
The hypotheses and target of each integral are part of its definition.
