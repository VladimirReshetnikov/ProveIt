# Local barriers at the large-cardinal frontier

Research continuation prepared for Vladimir Reshetnikov — 18 September 2026.

## Contents

- `Large_Cardinals_Research_Continuation.pdf` — the 19-page report.
- `Large_Cardinals_Research_Continuation.tex` — complete, standalone LaTeX source, including its bibliography.
- `build.sh` — rebuild with pdfLaTeX on Linux/macOS or a compatible shell.
- `build.ps1` — rebuild with pdfLaTeX from PowerShell.

The report continues the supplied `Large_Cardinals_Unified_Report.tex`. It retains that source's newpx text/math fonts, sans-serif settings, page geometry, heading styles, assessment boxes, and Forest/Olive/Sage/Pale color palette. The supplied original is cited as the starting report; it is not needed to compile the continuation.

## Principal results and locations

- **Theorem 3.4:** gamma-cover exactingness of lambda forces lambda to be regular in HCD(eta) for every cardinal eta strictly above gamma.
- **Theorem 4.2 and Corollary 4.3:** a strongly compact delta below lambda supplies a short cofinal set in HCD(delta) absent from every HCD(eta) above the cover bound. This yields conditional inconsistencies with precisely stated local stabilization principles.
- **Theorems 5.3–5.4:** forcing and Ground Axiom obstructions, including incompatibility of cover exactingness, the Ground Axiom, and a strongly compact cardinal above the cover bound.
- **Theorem 6.2:** at a fixed regular cardinal theta, the range j``theta of a nontrivial elementary embedding j:V -> M contains no unbounded subset belonging to M. The section separates this strengthening from the known stationary-spectrum reconstruction.
- **Theorem 7.2:** a derived equiconsistency with I0 places an ultraexacting cardinal at the first ordinal where V and HOD disagree about cofinality and powersets. This packages existing forcing and consistency results; it is not claimed as a new I0 construction.

## Status

The document gives conventional mathematical proofs and an explicit dependency audit. Imported results, including the July 2026 cover-exacting lecture notes, are identified separately from deductions in the continuation. The new-in-this-document deductions have not been independently refereed or formalized, and bibliographic priority is not asserted.

The report does not claim an unconditional resolution of cover-exacting–strongly-compact coexistence, ordinary exacting–extendible coexistence, I0, or the unrestricted global cardinal-preserving embedding problem.

## Building

Use a TeX distribution providing pdfLaTeX and the packages named in the source. In particular, the source uses `newpxtext`, `newpxmath`, `microtype`, `mathtools`, `titlesec`, `fancyhdr`, `tcolorbox`, `xurl`, and `hyperref`, as well as standard LaTeX packages. No separate bibliography tool or external image assets are required.

From this directory:

```sh
bash build.sh
```

or, in PowerShell:

```powershell
./build.ps1
```

Each script runs pdfLaTeX three times to resolve the table of contents, citations, and cross-references. Intermediate files are written under `_build`; the resulting PDF is copied next to the source.

## Artifact checks

The delivered PDF compiled to 19 pages. The final compilation had no undefined references/citations, missing-character reports, or overfull/underfull box warnings. All pages were rendered and visually inspected. These are document-production checks, not formal verification of the mathematical proofs.
