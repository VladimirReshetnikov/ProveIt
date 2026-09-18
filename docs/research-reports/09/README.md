# Large cardinals at the inconsistency frontier — research continuation

Prepared for Vladimir, 18 September 2026.

## Files

- `Large_Cardinals_Research_Continuation.pdf`: the typeset research report.
- `Large_Cardinals_Research_Continuation.tex`: its complete, standalone LaTeX source.
- `proof_dependencies.md`: a compact dependency and verification ledger.
- `build.ps1`: Windows PowerShell build script.
- `build.sh`: POSIX shell build script.
- `SHA256SUMS`: checksums of the files above.

The source preserves the supplied report's newpxtext/newpxmath typography,
Forest/Olive/Muted/Sage/Pale palette, page geometry, headings, theorem styles,
and assessment boxes. It needs no external graphics, bibliography database,
or copy of the original source to compile. No font files are distributed.

## Mathematical contents

The main result developed in the report is the Prikry-forcing refinement

    Con(ZFC + I3_wf(0)) => Con(ZFC + exists lambda CEx_lambda(lambda)).

The construction is stated in Theorem 5.2, with the set-model consequence in
Corollary 6.1. The internalization and finite-change family arguments are
Lemmas 3.1 and 4.1. The iteration-localization inputs and their source locators
are explicitly separated from those arguments.

Theorem 7.1 proves the definable-family obstruction: at an exacting lambda,
a nonempty OD_(V_lambda) family of short cofinal maps has a coordinate
projection of order type lambda. Therefore it cannot have cardinality below
lambda. Corollaries 7.2 and 7.4 state conditional inconsistency consequences.
Proposition 8.1 gives an associated fresh-sequence/approximation diagnostic.

These are research-draft proofs, not machine-checked or independently
refereed proofs. The main construction builds on existing iteration and
forcing methods. The cited 2026 notes already anticipate cover variants of
related constructions; historical priority is not asserted. No resolution
of the smaller-strongly-compact coexistence problem is claimed.

## Build

Install a LaTeX distribution with pdfLaTeX and the packages listed in the
source, notably newpx, amsmath, amsthm, mathtools, microtype, tcolorbox,
geometry, titlesec, fancyhdr, enumitem, tabularx, longtable, booktabs,
xurl, and hyperref. A reasonably complete TeX Live or MiKTeX installation
provides them.

On Windows:

    pwsh -File ./build.ps1

On a POSIX system:

    sh ./build.sh

The scripts run pdfLaTeX three times, place temporary files in `build/`,
and copy the finished PDF to this directory. No network access is required
once the packages are installed.

## Validation performed for this delivery

The source was compiled successfully with pdfLaTeX in three passes. The
final log has no undefined references, missing-character warnings, or
overfull/underfull box warnings. The PDF was rendered with Poppler and
visually inspected. The mathematical checks are described in the report
and dependency ledger; compiling or rendering the PDF is not mathematical
proof verification.
