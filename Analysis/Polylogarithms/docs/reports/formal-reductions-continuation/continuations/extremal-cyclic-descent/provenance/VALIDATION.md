# Validation record

Completed 10 October 2026 UTC for the delivered report.

## Source baseline

- Repository commit: `a0a90ef31877f98be437191c48b46f02d5456867`.
- 65 retrieved source objects, including 40 manuscript chapter sources and
  all 16 incoming archives present at that commit.
- Every recorded size and SHA-256 hash was checked against the local source.
- This is a source and dependency audit for the continuation, not a claim
  that every proof in the entire repository has been reverified.

## Exact replay

`python code/replay_all.py` passed all five groups from the package root:

1. Gaussian envelope: four certified derivative signs, a rational root
   bracket of width 10^(-26), and a maximum-value interval of width 10^(-45).
2. Inverse expansion: exact implicit substitution through every generalized
   exponent strictly below 2, including exponent collisions.
3. Cyclic distributions: 52 exact raw-matrix Smith checks, plus three
   explicitly excluded ramified examples.
4. Lerch shape: exact rational isolation of the k=2 and k=3 endpoint roots
   and whole-interval derivative bounds deciding both global shapes.
5. S6: independent regeneration of all 5,131 specified rows, exact integer
   annihilation, and a nonzero integer target pairing in 2,546 coordinates.

The detailed outputs are in `results/replay_log.txt` and
`results/replay_summary.json`; the original exact data and receipts are also
retained in their topic directories. The replay was tested with Python
3.12.14 and SymPy 1.14.0.

## Analytic review

Separate proof reviews checked the beta allocation change of variables,
strict covariance sign, critical endpoint measure, strict normalized Mellin
comparison, inverse coefficients and collisions, finite resolution and
fixed-complex reduction, character and jet descent, Lerch branch criterion,
and the scope and normalization of the S6 separator.

The secant proof was strengthened during review: Tonelli at N=1 identifies
the absolute Euler sum with the finite positive Gaussian integral for every
a,b>0, eliminating an unnecessary a+b>=1 restriction. A second review
confirmed that no hidden threshold assumption remained.

Independent review here means separate computations and mathematical review
passes within the preparation workflow. It is not external peer review or
proof-assistant certification.

## PDF and LaTeX

- 34 pages, A4, generated with pdfLaTeX and latexmk.
- Modular and combined-text source both compile successfully.
- Their extracted article text is identical (93,189 characters).
- No unresolved references, overfull boxes, LaTeX warnings, or pdfTeX warnings.
- Every page was rendered with Poppler at 83 dpi and visually inspected.
- Full-page inspections additionally covered the figures and the verification
  table. No clipping, overlaps, malformed formulas, or figure-label problems
  were found.
- The combined source retains the two external vector figures supplied in
  `figures/`; the ZIP contains every required build input.

## Diagnostic scope

The Gaussian quadrature comparisons, sampled inverse errors, minimum
coordinates, and both figures are diagnostics. They are not substituted for
the exact sign and enclosure proofs. The Lerch plot records an analytic
omitted-function bound while leaving floating rounding unenclosed.

The existing S6 period identity, persistent Lerch monotonicity for every
k>=3, and the optimal off-critical all-N Euler constant remain open in this
report. These limitations are repeated in the claim-status ledger.
