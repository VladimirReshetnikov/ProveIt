# The Set-Theoretic Content of Bounded Surreal Arithmetic

**Subtitle:** Hereditary-size universes, coherent bi-interpretations, axiom spectra, and extension rigidity  
**Date:** September 22, 2026  
**Length:** 31 PDF pages, including the title page, contents, and references

## Files

- `surreal_cutoffs.tex`: standalone LaTeX source with an internal bibliography.
- `surreal_cutoffs.pdf`: the compiled article, with linked contents and references.
- `finite_checks.py`: standard-library Python finite regression checks.
- `verification_report.json`: the executed finite-check results and their scope.
- `build_report.json`: document-production checks, separate from mathematical verification.
- `Makefile`: optional build and check commands.

## Main results developed in the article

Write B_lambda for the surreal ordered field of birthdays below an epsilon
number lambda, expanded by its birthday function. Write kappa(lambda) for the
least cardinal greater than or equal to lambda, and H_kappa for sets with
transitive closure of cardinality below kappa.

The article supplies explicit relation-code interpretations recovering exactly
H_{kappa(lambda)}. At cardinal cutoffs it gives a uniform bi-interpretation with
H_lambda; at noncardinal cutoffs the corresponding set structure also names
lambda. A definable collector recovers this extra cutoff. In particular, the
birthday expansion at epsilon_0 is bi-interpretable with hereditarily countable
sets. Small arithmetic certificates handle the reverse interpretation without
assuming Replacement inside H_kappa.

For epsilon numbers lambda < eta, the actual cutoff inclusion is elementary in
the birthday-field language exactly when both cutoffs are cardinals and
H_lambda is elementary in H_eta. This contrasts with the elementary inclusions
of all the corresponding ordered-field reducts.

Two explicitly defined principles are calibrated: birthday eternity is
Replacement at cardinal cutoffs, and fiber packing is the strong-limit
condition. Their conjunction selects worldly cardinal cutoffs, not necessarily
regular inaccessible cutoffs. Further results give a cardinal-sized detector
for new subsets in outer models and distinguish oriented surcomplex
bi-interpretation from mutual interpretation without a named imaginary unit.

## Prior work and novelty boundary

The GLOBAL bi-interpretation of surreal arithmetic with set theory was already
announced by Junhong Chen, Joel David Hamkins, and Ruizhi Yang. The article
credits that work, the classical epsilon-cutoff theorem, and ordinary
well-founded coding. It does not claim their discovery or a resolution of a
named longstanding conjecture.

The proposed contributions are the precise local refinements, especially
noncardinal cutoff recovery, the elementary-inclusion spectrum, the
singular-cardinal-safe axiom calibration, and the explicit extension detector.
Their formulations were not located in the inspected sources, but no exhaustive
priority claim is made. They may overlap unpublished details of prior research.
The proofs are written mathematical arguments, not peer review or proof-assistant
certificates. No Lean development is supplied.

The repository comparison was pinned to:

    VladimirReshetnikov/Surreal
    4f2645599121fa872c7104995e47f86f0382351f

The inspected material was the report catalog, relevant portions of the
foundations report, and the surcomplex-automorphism report's scope. Repository
search was not a dependable exhaustive full-text index. No complete repository
build or theorem inventory was performed, and no repository files were modified.
Section 13 and the bibliography document the scope and source distinctions.

## Build

Use a TeX installation with the packages listed in the source preamble. No
external graphics, font files, BibTeX database, shell escape, or network access
is needed. From this directory run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_cutoffs.tex

Alternatively, run the following command three times:

    pdflatex -interaction=nonstopmode -halt-on-error surreal_cutoffs.tex

Run the finite checks with Python 3.10 or later:

    python3 finite_checks.py

The script writes `verification_report.json` next to itself and stops with an
error if an assertion fails. These commands are also available as `make pdf`
and `make check`.

## Executed checks

The supplied PDF compiled with zero LaTeX warnings, unresolved citations or
references, and overfull/underfull box warnings in the final log. All pages were
rendered and inspected in contact sheets, with selected proof pages inspected
at larger scale. A coordinate check found no text outside the tested page
margins.

The finite run passed 16,129 prefix tests, 642 bit tests, 11,440 finite pairing
checks, and exhaustive relation tests on domains of size at most three. Among
15 valid rooted codes, all 225 ordered pairs passed both equality and membership
checks. A negative regression confirms that omitting predecessor fullness admits
a false membership witness.

These are document-production and finite-regression checks only. They do NOT
certify the transfinite proofs, large-cardinal statements, or historical novelty.
No third-party manuscripts or font files are redistributed.
