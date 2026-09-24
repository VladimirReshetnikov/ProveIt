# Maximal rigidity and finite symmetry from one measurable

A research continuation of the reports supplied in Cardinals4.zip.
Prepared 18 September 2026 for Vladimir Reshetnikov.

## Files

- `Maximal_Rigidity_and_Finite_Symmetry.tex`: self-contained LaTeX source.
- `Maximal_Rigidity_and_Finite_Symmetry.pdf`: compiled 21-page article.
- `finite_audit.py`: optional standard-library Python finite sanity checks.
- `finite_audit_results.json`: results of the delivered finite-check run.
- `README.md`: this guide.

## Principal results and reading guide

The setting is ordinary normal Prikry forcing at a measurable kappa in a
ZFC ground model W. The extension is V = W[C].

- Theorem 1.3 (page 3): the combined construction and its precise parameter
  allowance, including a single indexed family of all constructed classes.
- Section 4 (pages 7-8): 2^kappa jointly rigid quotient classes, with pairwise
  almost-disjoint representatives; every permitted definable complete section
  has 2^kappa full fibres.
- Theorem 5.1 (page 9): the one-point stem-splicing proof of the previously
  missing Prikry-model finite-label necessity. Together with Section 6, this
  gives the exact elementwise-fixed-label classification.
- Theorem 7.1 (pages 11-12): no nonempty finite definable family of r-of-n
  selectors, without assuming any member of the family is definable.
- Theorem 8.3 and Proposition 8.5 (pages 14-15): a common fixed-parameter HOD
  core recovers all ground subsets of kappa and the original normal measure;
  the core computes kappa+ correctly, and its Prikry layer captures the entire
  V_(kappa+1) of the ambient extension.
- Corollary 9.3 (page 17): starting at the least measurable, these conclusions
  coexist with no ambient measurable, exacting, or ultraexacting cardinal at
  or below kappa.
- Theorem 9.5 and Corollary 9.6 (page 18): the strengthened quotient package,
  expressly including an internal normal-measure clause, and its rank-capture
  strengthening are equiconsistent with one measurable cardinal.

## Scope and verification

The article gives detailed conventional English proofs. Its new contributions
are claimed relative to the supplied synthesis, not as a certification of
worldwide priority. The proofs have not been independently refereed or
formalized in Lean. The provided Lean development was reference material;
it is not represented as a formal certificate for the new forcing arguments.

The Prikry-model finite-label question is answered. The implication from
arbitrary rigidity alone, and the maximum-size conclusion for every
ultraexacting cardinal, are not asserted. No inconsistency of an ordinary
large-cardinal axiom is claimed. The equiconsistency lower bound uses the
explicit internal normal-measure clause, not finite symmetry alone.

The finite audit passed:

- 120,936 phase-identity instances;
- 40,319 least-common-multiple exponent instances;
- 132 block-cycle instances;
- five exhaustive finite selector instances;
- the five-label S_3 example.

These finite computations are not a verification of forcing, HOD, or the
infinite set-theoretic theorems.

The PDF was compiled successfully with all cross-references resolved and no
LaTeX overfull/underfull box warnings. All 21 pages were rendered for layout
inspection; text was also checked for unresolved reference placeholders and
out-of-page bounding boxes.

## Rebuilding the article

A TeX installation with `newpxtext`, `newpxmath`, `tcolorbox`, `titlesec`,
`fancyhdr`, `microtype`, `enumitem`, `mathtools`, `xurl`, and the other packages
listed in the preamble is required. The source uses the supplied synthesis's
New PX text/math setup and Forest/Olive/Muted/Sage/Pale colour definitions.

Using latexmk:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Maximal_Rigidity_and_Finite_Symmetry.tex
```

Or run pdflatex three times to settle the contents and cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Maximal_Rigidity_and_Finite_Symmetry.tex
pdflatex -interaction=nonstopmode -halt-on-error Maximal_Rigidity_and_Finite_Symmetry.tex
pdflatex -interaction=nonstopmode -halt-on-error Maximal_Rigidity_and_Finite_Symmetry.tex
```

## Rerunning the finite audit

Python 3.10 or later; no third-party modules are needed.

```sh
python3 finite_audit.py --output finite_audit_results.json
```

External references and attribution to the supplied reports are included in
the article's bibliography. The original archive and its Lean files are not
modified or bundled into this continuation.
