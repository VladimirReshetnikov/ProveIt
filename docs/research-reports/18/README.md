# Cofinal-orbit rigidity at the ultraexacting boundary

Research continuation prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Cofinal_Orbit_Rigidity.tex`: complete, standalone LaTeX source, with an inline bibliography.
- `Cofinal_Orbit_Rigidity.pdf`: compiled report, including detailed proofs and a proof-audit appendix.
- `build.sh`: a three-pass pdfLaTeX build script.
- `PROOF_STATUS.md`: a compact statement of the mathematical contribution, dependencies, and limitations.

The source uses the supplied reports' New PX text and mathematical fonts, page geometry, forest/olive/sage palette, theorem styling, and shaded assessment boxes. Font files are not included.

## Main result

Let lambda be ultraexacting. Let D_lambda be the cofinal subsets of lambda of order type omega, and identify two such subsets when their symmetric difference is finite. There is an equivalence class q such that every nonempty family A of short cofinal subsets of lambda, ordinal definable from q and finitely many parameters in V_lambda, has cardinality at least lambda. The family q itself attains the bound.

One consequence is that every complete section definable from these parameters meets this same q in exactly lambda representatives. Another excludes definable families of fewer than lambda homomorphisms from finite-difference equivalence into definable equivalence relations on D_lambda with all classes smaller than lambda. Neither result assumes a uniform size bound below lambda.

Allowing q as one set parameter does NOT allow an arbitrary member of q as a parameter.

## Build

A reasonably complete TeX Live or MiKTeX installation with pdfLaTeX is required. The packages include `newpxtext`, `newpxmath`, `amsmath`, `amsthm`, `mathtools`, `microtype`, `geometry`, `xcolor`, `tcolorbox`, `titlesec`, `fancyhdr`, `enumitem`, `booktabs`, `tabularx`, `longtable`, `xurl`, and `hyperref`. Their ordinary dependencies are resolved by the TeX distribution.

On a Unix-like system, run:

```sh
bash build.sh
```

Or compile the source three times with pdfLaTeX:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Cofinal_Orbit_Rigidity.tex
pdflatex -interaction=nonstopmode -halt-on-error Cofinal_Orbit_Rigidity.tex
pdflatex -interaction=nonstopmode -halt-on-error Cofinal_Orbit_Rigidity.tex
```

No external bibliography file, downloaded paper, image, private font file, or network access is needed to build the report. Hyperlinks in the bibliography are not build dependencies.

## Status

The report provides conventional mathematical proofs after explicitly stated external inputs. It is not refereed or machine-checked. The extensions go beyond the corresponding assertions in the supplied synthesis; published priority is not claimed.

The I0/ultraexacting equiconsistency and the preservation/coding theorem used for calibration are imported results of Aguilera, Bagaria, Goldberg, and Luecke. This report does not claim a new comparison of the consistency strengths of those standard axioms, or an unconditional inconsistency of either one.
