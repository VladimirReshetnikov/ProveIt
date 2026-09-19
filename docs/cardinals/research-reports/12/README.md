# Maximal-width uniformization at ultraexacting cardinals

Research continuation prepared on 18 September 2026 for Vladimir Reshetnikov.

## Main files

- `Maximal_Width_Uniformization.tex`: complete, self-contained LaTeX source.
- `Maximal_Width_Uniformization.pdf`: compiled 21-page report.
- `build.sh`: three-pass PDF build, using a temporary directory.
- `checks/verify_combinatorics.py`: exact finite-combinatorics checks.
- `checks/results.txt`: actual output of the checks included in this archive.

The input `Cardinals2.zip` contained two TeX reports, named
`Large_Cardinals_Synthesis.tex` and `Large_Cardinals_Unified_Report.tex`.
They are cited in the new report but are not duplicated in this archive.

## Principal result

Let lambda be ultraexacting and let D_lambda consist of the cofinal subsets of
lambda of order type omega. A complete section T meets every equivalence class
modulo finite symmetric difference.

For every such T definable from ordinal parameters and a parameter in V_lambda,
at least lambda classes q have the following property. For every reference
representative a in q and every integer r, the phase subfamily

    {b in T intersect q : |b minus a| - |a minus b| = r}

has cardinality lambda. On the same classes, a single coordinate threshold works
for all phases: each sufficiently late coordinate projection in every phase is
cofinal in lambda and has cardinality lambda.

In particular, an ultraexacting lambda is incompatible with a definable complete
section having strictly fewer than lambda representatives in each class. It is
also incompatible with a definable complete section having a proper integer
spectrum in each class, even when the fibers already have maximal size.

Further results address small definable families of transversals, explicitly
fixed Icarus enrichments, the low-rank/bounded versus cofinal choice boundary,
and consistency calibration by the known ultraexacting/I0 equiconsistency.

## Status and dependencies

The new deductions are proved in the report. They extend the supplied reports;
publication priority in the wider literature is not certified. The conventional
proofs have not been independently refereed or formalized in a proof assistant.
No inconsistency of bare ultraexactingness, I0, or I0-sharp is claimed.

The main proof imports local Kunen inconsistency and the established
ultraexacting witness-control lemma. The consistency section additionally imports
the existing ultraexacting/I0 equiconsistency and low-rank coding forcing theorem.
Their precise references and theorem numbers are supplied in the paper.

## Rebuilding

Requirements: `pdflatex` and a TeX installation providing the packages named in
the source, in particular `newpxtext`, `newpxmath`, `tcolorbox`, `titlesec`,
`microtype`, and `hyperref`. No external bibliography database or graphics are
needed. The typography and forest/olive/sage colors match the supplied reports.
No separate font files are included.

From this directory, run:

    bash build.sh

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error
Maximal_Width_Uniformization.tex` three times. Three passes resolve the table of
contents and cross-references.

## Running the checks

Requires Python 3.10 or later, with no external packages:

    python3 checks/verify_combinatorics.py

The script performed 410,533 exact checks on finite modifications of the
infinite even natural numbers. It checks the index cocycle, reference changes,
reference deletions, the sign of the phase shift, a coordinate inequality, and
finite cyclic translation invariance. It does not verify elementary embeddings,
reflection, or any large-cardinal consistency claim. The finite cyclic checks
are finite analogues, not a simulation of the theorem about all integers.

## PDF checks

The delivered PDF was compiled without LaTeX warnings or overfull boxes.
All pages were rendered for visual inspection. The document includes embedded
font subsets, a linked table of contents, numbered theorem references, and
bibliographic links. Build intermediates are not included in the archive.
