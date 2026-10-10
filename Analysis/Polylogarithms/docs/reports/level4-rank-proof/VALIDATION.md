# Validation record

## Exact mathematics and software

The final run of `python code/verify.py` completed successfully with the
pinned requirements. Its machine-readable receipt is
`data/verification_report.json`. It checks 40 weights (2–41), 20 odd-weight
nullspaces and S-family witnesses, 210 even-weight formulas against all 816
retained product rows, 420 Gaussian membership cases, six odd affine
compatibility cases, and 16 mixed leading-family comparisons. Weight-five
ranks are also checked by exact rational elimination.

The fixed-prime rank lower bounds are combined with independent, explicitly
constructed integer kernel upper bounds. Thus the finite certificates concern
ranks over Q, not numerical ranks. The all-weight theorems are proved in the
article by polynomial reflection, independently of the extent of the finite
census. The certificate construction uses integer/rational arithmetic; it does
not use floating point, PSLQ, or an assumed independence of period atoms.

The software was tested with Python 3.13.5, SymPy 1.14.0 and NumPy 2.3.5.
The final recorded exact run took about 20 seconds in the delivery environment.
This timing is not a portable benchmark or an asymptotic complexity claim.

## Separate numerical diagnostics

`python code/numerics.py` passed all 54 direct nested-series comparisons
at 70 working decimal digits and 4096 outer terms. The maximum ratio of the
observed discrepancy to the analytic absolute-tail bound was 0.79673172.
The script uses mpmath 1.3.0 without outward rounding. This is deliberately
labeled diagnostic evidence, not a rigorous numerical enclosure or proof of
a numerical identity.

## Local integration checks

`python code/test_integration.py` passed six checks on synthetic temporary
fixtures: the known Git empty-blob hash, changed-source refusal, nonmutating
dry-run preparation, exact opt-in output bytes, repeat refusal after the
canonical file changes, and refusal to overwrite an existing fragment.
No actual repository was modified during these tests.

The integration fragment compiled in a representative A4 book wrapper as
four pages. The final wrapper log has no unresolved references or overfull
boxes. All four wrapper pages were rendered and visually inspected. This is
not a build of the full canonical 228-page manuscript.

## Article production checks

The delivered article was compiled in three final pdfLaTeX passes. The final
log has no LaTeX warnings, unresolved references, overfull boxes or underfull
box warnings. The PDF has 17 pages. All pages were rendered with the supplied
PDF rendering utility and inspected in contact sheets; selected mathematical
proof and formula pages were also inspected at full size. No clipping,
overlaps or missing glyphs were observed. Build metadata and hashes are in
`data/pdf_build_report.json`.

The integration proof and the article agree on the matrix vocabulary,
completion sign, polynomial substitutions, rank formulas, coefficient order,
and mixed leading-index identities. A final notation pass corrected local
u-versus-nu and variable-case typographical inconsistencies in this new draft
before release; these were not errors attributed to the source manuscript.

## Trust boundary

The analytic product laws are ordinary mathematical prerequisites, and the
rank proof is an ordinary mathematical proof. Neither has been formally
checked in Lean. The article has not received independent peer review.
The S4 evaluation, numerical period independence and worldwide novelty of
individual special-value identities remain outside the claims. The remote
repository is unchanged.
