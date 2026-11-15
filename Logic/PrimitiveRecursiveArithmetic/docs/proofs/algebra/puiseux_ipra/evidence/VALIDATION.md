# Validation record

Date: 15 November 2026.

## Mathematical review

The integrated argument was reviewed for the distinction between exact
algebraic input presentations and arbitrary Cauchy names; primitive
recursive uniformity in the polynomial degree; bounded valuation searches;
degree decrease in the Newton tree; finite precision losses; multiplicity
accounting; convergence and pole bounds; and the object-theory target.
The accompanying audit notes record the principal checks and limitations.

The human-readable result is for the exact-input theorem stated in the
report. The report also proves the obstruction to a uniform exact Puiseux
coefficient constructor on arbitrary primitive recursive Cauchy input
names. It does not assert that every possible arithmetization of an
unrestricted analytic existence statement is unprovable in iPRA.

The reused one-root FTA argument is included in full and was reviewed for
the particular fixed-evaluator application made here. The exact algebraic
splitting construction is supplied separately in the new report. Neither
the mathematical review notes nor the frozen dependency are a
kernel-checked iPRA derivation.

## Executable finite checks

Command:

    python3 code/check_examples.py --cutoff 96 --output evidence/example_checks.json

Result: all checks passed, using exact Gaussian-rational arithmetic and
only the Python standard library.

The five examples cover a cusp, ramification four, repeated factors,
Laurent poles, and high contact. Complete factorization products with the
stated multiplicities were checked through T-degree 96. The nonpolynomial
examples also check their implicit coefficient recurrences and finite
weighted majorant bounds. The recorded JSON contains the parameters and
first nonzero terms.

These are finite consistency checks. The program is not a general
Newton-Puiseux solver, and these examples do not prove the universal
theorem.

## PDF production and visual checks

The supplied main TeX and its three included section files compile to the
supplied 22-page PDF. The final build used pdfTeX through latexmk with
halt-on-error. There are no errors, unresolved references, or overfull
boxes in the final compilation log. Ordinary underfull-box notices from
long source references do not affect readability.

All pages were rendered to PNG for visual inspection. The complete layout
was reviewed in page contact sheets, with final title, contents, technical
body, and source-accounting pages inspected separately. Equations, tables,
page breaks, and references are legible and contained within the margins.
The PDF fonts are embedded.

The build environment needed a private pdfLaTeX format and font map because
its TeX distribution had no initialized format cache. These temporary
runtime files are not part of the deliverable; a normal TeX Live
installation uses the standard build command in README.md and Makefile.

## Lean status

No Lean or Lake executable was available, so no Lean compilation or
kernel verification was performed. The supplied Lean file is explicitly
an uncompiled interface and outline against the inspected ProveIt
snapshot. It does not contain a Puiseux derivation.

The completion target is a term of

    Prf PRAAx [] (PuiseuxSentence concretePrograms)

with concrete primitive-recursive programs and proved decoding contracts.
The conditional transport theorem in the interface only transports a
derivation once supplied. The detailed roadmap identifies the remaining
algebraic, analytic, and deep object-theory proof modules, including the
FTA derivation.

## Packaging

The archive includes the complete new report sources and PDF, the Lean
outline and roadmap, the exact example checker and results, source and
review records, and the unchanged extracted FTA dependency. Build logs,
auxiliary TeX files, rendered page images, caches, and runtime helpers are
excluded. SHA256SUMS covers every included regular file except itself.
