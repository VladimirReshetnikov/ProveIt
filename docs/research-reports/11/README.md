# Large cardinals: quotient parameters and sharp uniformization barriers

Research continuation prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Large_Cardinals_Quotient_Continuation.pdf`: the 20-page report.
- `Large_Cardinals_Quotient_Continuation.tex`: complete, standalone LaTeX source;
  the bibliography is included in the source.
- `build.sh` and `build.ps1`: Unix-shell and PowerShell build scripts.
- `SHA256SUMS.txt`: checksums of the distributed files.

## Main results and reading guide

The background notation is in Section 2. All sizes are ambient ZFC sizes.

1. **Theorem 5.2:** At an ultraexacting cardinal lambda, no function ordinal
   definable from low-rank parameters assigns to every finite-difference class
   a nonempty family of fewer than lambda short cofinal subsets of lambda.
   The outputs need not represent the input class.
2. **Theorem 5.4:** Every such definable transversal meeting every class has a
   fiber of size exactly lambda. This strengthens the finite-valued obstruction
   in the supplied synthesis and is sharp.
3. **Theorem 6.2 and Corollary 7.4:** Some finite-difference classes can be named
   without making lambda singular in the hereditary-definability model, even
   when arbitrary parameters from V_lambda are also allowed. There are at least
   lambda distinct such classes; lambda of them can induce the same model.
4. **Proposition 7.2:** A separate explicit, redundant coding construction
   produces classes that DO recover a cofinal omega-sequence. Not every class
   preserves the regularity conclusion.
5. **Theorem 8.1:** A self-embedding preserving a thin transversal in an inner
   model containing V_{lambda+1} is impossible under the stated critical-sequence
   assumptions.
6. **Theorem 9.2:** Adding the quotient-parameter profile to ultraexactingness
   and V_lambda contained in HOD gives a theory equiconsistent with I0. This
   calibration uses the existing ultraexacting/I0 comparison and coding theorem;
   it does not claim a new large-cardinal strength bound.

IMPORTANT PARAMETER CONVENTION: a quotient class q is allowed as ONE named set
parameter. Its individual members are not separately allowed as parameters.
The good q is not an element of its own hereditary-definability model. The
report defines N_q and H_q explicitly; these must not be replaced by L(q),
L[q], or a convention that hereditarily adjoins all members of q.

## Status and scope

The report supplies detailed conventional proofs and a dependency/failure-mode
review in Section 10. The extensions are new relative to the two supplied
reports. Priority over the broader literature is not claimed. The mathematics
is unrefereed and has not been checked in a proof assistant.

The inconsistencies concern extra uniformization/recovery/preservation
principles together with the stated embedding hypotheses. No inconsistency of
ultraexacting existence alone is claimed. The open question about countable
families of selector FUNCTIONS is not the same as the small-family theorem
proved here and is not settled by it.

External inputs are explicitly isolated and cited: local Kunen inconsistency;
the high-critical-point ultraexacting witness characterization; and, only for
the consistency calibration, the ultraexacting/I0 comparison and the forcing
that preserves ultraexactingness while making V_lambda a subset of HOD.

## Build

Use pdfLaTeX from a TeX Live or MiKTeX installation with the packages listed in
the preamble, including newpxtext, newpxmath, microtype, tcolorbox, titlesec,
fancyhdr, hyperref, and xurl. No separate BibTeX run is needed.

On Unix-like systems:

    sh ./build.sh

In PowerShell:

    ./build.ps1

The scripts compile into `.build/`, run four passes for references and the table
of contents, then copy the resulting PDF next to the source. They require
`pdflatex` to be on PATH. They do not download or install dependencies.

The original preamble's Palatino-style New PX text/math, sans-serif accents,
Forest/Olive/Sage/Pale palette, margins, theorem style, and assessment boxes are
preserved. Font files are not distributed.

## Validation performed for this release

- pdfLaTeX compilation completed with no warnings, undefined references,
  missing-character reports, or overfull/underfull boxes in the final log.
- The table of contents and bibliography destination were checked after the
  final pagination pass.
- The PDF was rendered with Poppler (`pdftoppm`), and the page layouts were
  visually inspected against the supplied synthesis's typography and palette.
- Artifact validation is separate from verification of the mathematical proofs.

## Input provenance

The uploaded `Cardinals2.zip` contained the two TeX sources
`Large_Cardinals_Unified_Report.tex` and `Large_Cardinals_Synthesis.tex`.
The continuation is standalone and does not require either input file to build.
The earlier reports are cited in its bibliography but are not repackaged here.
