COVER-EXACTING CARDINALS AND THE GROUND AXIOM
Research continuation — 18 September 2026

CONTENTS
  Large_Cardinals_Research_Continuation.tex
  Large_Cardinals_Research_Continuation.pdf
  README.txt

The PDF is an 18-page research note continuing the supplied
Large_Cardinals_Unified_Report.tex. The original report is not modified
or included in this archive. The source is self-contained, with an inline
bibliography and no external figures or data files.

MAIN DEDUCTIONS
  1. If lambda is gamma-cover exacting, then lambda is regular in
     HCD(gamma^+), despite having cofinality omega in V. Every HCD(gamma^+)
     cover of an ambient countable cofinal subset of lambda has ambient
     size at least lambda.
  2. A strongly compact delta below lambda forces a strict separation
     between HCD(delta) and HCD(gamma^+) already on subsets of lambda.
     Coexistence is therefore inconsistent with the stated local
     stabilization hypothesis.
  3. A strongly compact delta above gamma makes HCD(delta) a proper
     set-forcing ground. Coexistence is therefore inconsistent with the
     Ground Axiom. Every forcing representation from this ground fails
     the lambda-chain condition in that ground and has the size/density
     lower bounds stated in the report.

STATUS
These are conventional mathematical deductions from the explicitly cited
background results. They are not an unconditional refutation of cover
exactingness. Priority of the exact formulations has not been established;
the note is not independently peer-reviewed or proof-assistant verified.
The original strongly-compact-below coexistence problem is not resolved
without the additional hypothesis. See Sections 1 and 9 and Appendix A
for the precise claims and limitations.

BUILD
Use a TeX installation with the packages listed in the source preamble,
including newpxtext, newpxmath, tcolorbox, titlesec, fancyhdr, and hyperref.

  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    Large_Cardinals_Research_Continuation.tex

Alternatively, run pdflatex repeatedly until all cross-references and the
table of contents stabilize. No separate BibTeX step is required.

The source retains the supplied report's font configuration, page geometry,
heading and box styles, and Forest/Olive/Muted/Sage/Pale color definitions.
Font files are not included.

VALIDATION
The included source was successfully compiled with pdfLaTeX and latexmk.
The final compilation log had no warnings, missing references, overfull or
underfull boxes, or errors. All pages were rendered and inspected; the
revised end pages were checked after the final pagination adjustments.
Compilation and visual checks do not constitute verification of the
mathematical theorems.
