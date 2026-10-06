# Sources and provenance

The Report135 article is the reader-facing proof document. Report134 and its
unchanged full eight-file companion are included under `companion134/`; these
supply the inherited exact tableau/gluing identity, nonnegativity, global
bounds, and original finite lower certificate. Nothing in that release has
been edited. Top-level new code is a compact independent reimplementation of
the algebraic encodings and correction diagnostics, not a copy of research
logs or unreviewed assertion files.

The exact integer fixture u_0 through u_20 is recomputed from the inherited
formula. The prefix through n=15 agrees with the original frozen OEIS fixture,
whose source is https://oeis.org/A217057 (retrieved 2026-10-02). The remaining
five values are outputs of the exact formula, not attributed to a new OEIS
retrieval. Finite R/S data are exact fractions from that same formula plus the
new explicitly checked transform identities through both correction orders.
The exact positive logarithmic contraction is checked independently using
bivariate Euler moments. No external data download is
needed to reproduce any calculation.

Primary mathematical references used by the article include:

- A. Bostan, P. Lairez, B. Salvy, *Multiple binomial sums*, Journal of Symbolic
  Computation 80 (2017), 351–386. DOI: https://doi.org/10.1016/j.jsc.2016.04.002
  Author version: https://arxiv.org/abs/1510.07487 (v2 contains Definition 1.1,
  Proposition 3.12, Theorem 3.5 and Corollary 3.6)
- E. M. Rains, *Increasing Subsequences and the Classical Groups*, Electronic
  Journal of Combinatorics 5 (1998), R12. Primary repository record:
  https://authors.library.caltech.edu/records/xrxyg-v6r72
- Regev's strip-sum leading constant and the original occurrence decomposition
  are referenced and explained in Report134

The bundle redistributes the two reports and their computational companions,
not third-party PDFs. Published closure theorems and asymptotic arguments are
cited inputs whose hypotheses must be verified in the articles; finite replay
is not a machine-checked proof of those theorems.
