# Large cardinals at the inconsistency frontier II

**Cofinality barriers for cover-exacting cardinals: local HCD separation and conditional inconsistency**  
Prepared for Vladimir Reshetnikov · 18 September 2026

## Contents

- `Large_Cardinals_Continuation.pdf`: the compiled 17-page report.
- `Large_Cardinals_Continuation.tex`: self-contained LaTeX source, including bibliography.
- `build.sh`: a two-pass pdfLaTeX build script.
- `README.md`: this file.

This is a continuation of the supplied `Large_Cardinals_Unified_Report.tex`, not an edited replacement. The original report is unchanged and is not required to compile this continuation. The continuation retains its document geometry, newpx text and mathematics, sans-serif headings, theorem formatting, Forest/Olive/Sage/Pale color palette, and assessment boxes.

## Main deductions

1. If lambda is gamma-cover exacting and eta > gamma, then no short cofinal subset of lambda is ordinal definable from finitely many eta-complete ambient ultrafilters on ordinals. Consequently lambda is regular in HCD(eta), while its ambient cofinality is omega.
2. A strongly compact delta < lambda forces a cofinal witness to the strict local difference between HCD(delta) and HCD(gamma+). A precisely stated local promotion principle is therefore inconsistent with this configuration.
3. A strongly compact theta > gamma makes HCD(theta) a proper set-forcing ground of the universe. Thus this configuration is inconsistent with the Ground Axiom. The report also derives forcing-size and approximation obstructions.

The source theorems used in these deductions are identified separately, and all deductions are proved in the report. The ultrafilter-recovery mechanism is already in Blue–Goldberg's 2026 lecture notes; Goldberg's published HCD theorems are essential inputs. Historical priority of the resulting formulations and corollaries has **not** been established. The bare open problem of cover exactingness above a strongly compact cardinal is **not** resolved here. There is no claimed new forcing construction or newly determined exact equiconsistency.

These are conventional mathematical proofs, not proof-assistant-verified results. The report includes an explicit hypothesis and proof audit.

## Build

Use a TeX distribution with pdfLaTeX and the packages named in the source, including `newpxtext`, `newpxmath`, `tcolorbox`, `titlesec`, `fancyhdr`, and `hyperref`. A reasonably complete TeX Live installation is suitable.

From this directory:

```sh
./build.sh
```

Or run twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Large_Cardinals_Continuation.tex
pdflatex -interaction=nonstopmode -halt-on-error Large_Cardinals_Continuation.tex
```

No BibTeX run, external images, custom font files, or network access is required to compile. A build creates ordinary LaTeX auxiliary files alongside the source. These intermediates and third-party source PDFs are not included in the archive.

## Checks performed

The supplied PDF was compiled successfully, with resolved references and no reported LaTeX warnings or overfull/underfull boxes in the final build. All 17 pages were rendered for layout inspection. The bibliography records the primary-source versions and theorem numbering used.
