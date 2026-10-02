# Source audit

Access date: 1 October 2026.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected tree: `bc4d1fa2b849b644461e3b8c597d77aa1c54b9fe`.

Baseline article:
`SetTheory/Cardinals/docs/reports/hankel-determinants/growth-and-runs/apery-hankel-determinant-growth/apery_hankel_growth.tex`

Title: *A proof of the Apéry Hankel growth conjecture* (18 September 2026).
This establishes the quadratic logarithmic growth, including an O(n)
remainder, and leading varying-shift results. Those are prior results for
the purposes of the present report. The repository tree and relevant article
were read using the connected GitHub tools.

## Primary mathematical sources

1. OEIS A005259 — definition and recurrence for Apéry numbers:
   https://oeis.org/A005259
2. OEIS A228143 — Hankel determinant sequence and source status:
   https://oeis.org/A228143
   The accessed entry still labels the leading n-squared-root limit as a
   conjecture, although the repository article above proves it. The present
   report does not claim that old limit as new.
3. Kotesovec's ratio plot linked by A228143:
   https://oeis.org/A228143/a228143.jpg
   The sharper target is suggested by this plot; it is not described in this
   report as a separately worded conjecture in an OEIS formula field.
4. G. A. Edgar, *The Apéry Numbers as a Stieltjes Moment Sequence*,
   arXiv:2005.10733v2:
   https://arxiv.org/abs/2005.10733
   https://arxiv.org/pdf/2005.10733
   Theorem 1, Proposition 4, Propositions 23, 25–26, and Corollary 27 supply
   the moment density, positivity, local behavior, and hypergeometric formulas.
   Relevant mathematical formulas and the density figure were inspected.
5. B. Simon, *OPUC on One Foot*, Bulletin of the AMS 42 (2005), 431–460:
   https://arxiv.org/abs/math/0502485
   DOI: 10.1090/S0273-0979-05-01075-X.
   Classical unit-circle orthogonal-polynomial context. The exact minimum
   argument and normalizations used here are presented in the new article.
6. P. Deift, A. Its, I. Krasovsky, *Asymptotics of Toeplitz, Hankel, and
   Toeplitz+Hankel determinants with Fisher–Hartwig singularities*,
   Annals of Mathematics 174 (2011), 1243–1299:
   https://annals.math.princeton.edu/2011/174-2/p12
   A comparison framework for further research only. Its theorems are NOT
   invoked to assert an unverified Apéry prefactor or all-orders expansion.

## Novelty-search scope

Searches included combinations of “Apéry”, “Hankel”, “ratio asymptotics”,
“Szegő constant”, and the A228143 identifier, together with a comparison to
the repository's existing Apéry growth article. No source inspected supplied
the present explicit ratio constant or the present Apéry envelope formulas.
This is a bounded literature audit, NOT evidence sufficient for an absolute
claim of bibliographic priority. Many nearby search results concern Hankel
determinants of zeta values rather than Hankel determinants of Apéry numbers;
these are different objects and were not substituted for the target.

No third-party source text, PDF, or font file is redistributed in this package.
