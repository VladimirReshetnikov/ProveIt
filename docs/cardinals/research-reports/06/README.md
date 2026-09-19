# Cover-exacting cardinals and high-completeness cores

Research continuation prepared for Vladimir Reshetnikov, 18 September 2026.

## Contents

- `Cover_Exacting_High_Completeness_Cores.tex`: self-contained LaTeX source.
- `Cover_Exacting_High_Completeness_Cores.pdf`: compiled 19-page report.
- `README.md`: build instructions and mathematical status.

## Build

Run these commands in the directory containing the source:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Cover_Exacting_High_Completeness_Cores.tex
pdflatex -interaction=nonstopmode -halt-on-error Cover_Exacting_High_Completeness_Cores.tex
```

A standard TeX Live or MiKTeX installation needs the packages named in the
preamble, including newpxtext, newpxmath, tcolorbox, titlesec, and hyperref.
The bibliography is included in the source; no BibTeX run or external figures
are required. No font files are distributed in this archive.

## Mathematical outcome

The report develops a high-completeness definability obstruction for
cover-exacting cardinals. It derives local-stabilization and cofinal-refinement
incompatibilities above a strongly compact cardinal, and a separate
incompatibility between cover exactingness and the Ground Axiom in the
presence of a proper class of strongly compact cardinals. It also proves a
singular-completeness endpoint, a ground-forcing antichain lower bound, and a
conditional first-regularization calculation.

The localized Kunen inconsistency and the published Goldberg theorems on
HCD cores are explicitly identified external inputs. Known lemmas are not
advertised as newly discovered. Historical novelty of the assembled
corollaries has not been established; the report has not been independently
refereed or machine-formalized. It does not claim an unconditional refutation
of cover-exacting cardinals above a strongly compact cardinal, nor a new
equiconsistency classification.

## Production checks

The source was compiled with pdfLaTeX. The final compilation had no undefined
references, overfull boxes, or LaTeX warnings. The PDF was rendered and visually
inspected; bibliography links and the table of contents are included.
