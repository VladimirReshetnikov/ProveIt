# Target and source audit

Checked on 19 September 2026.

## Target

Ce Xu and Jianqiang Zhao, *Rational Approximations for Reciprocals of
Multiple Zeta Values and Trivariate Cauchy Numbers*, arXiv:2609.11072v1,
submitted 10 September 2026, 24 pages.

- Abstract and version record: https://arxiv.org/abs/2609.11072v1
- Full HTML: https://arxiv.org/html/2609.11072v1
- PDF: https://arxiv.org/pdf/2609.11072v1

The higher-order generating function is equation (2). Theorem 1.1
establishes eventual alternation for fixed order. Section 6 treats the
exact onset, and Conjecture 6.1 appears on printed page 13 (PDF page
index 12). It places Gr(ell) between 0.47*3^ell and 0.477*3^ell for
ell >= 5. The nearby paragraph reports Gr(5)=113, among other small
thresholds. Both the conjecture and that paragraph were visually checked
in the rendered source PDF.

The source's initial existence theorem does not explicitly use the word
“least”; its later discussion of exact values does. The present article
makes the minimal-threshold interpretation explicit. Arbitrary nonminimal
bounds do not specify a unique sequence.

The auxiliary polynomial H_ell is given in Lemma 4.1 on printed page 7;
that definition was also visually checked. The elementary closed-form
roots in the new article follow directly from the binomial theorem.

## Background references

NIST DLMF Chapter 5:
- https://dlmf.nist.gov/5.5 (gamma recurrence, reflection, log-convexity)
- https://dlmf.nist.gov/5.7 (series expansions)
- https://dlmf.nist.gov/5.11 (asymptotic expansions)

OEIS records for the classical coefficient numerators and denominators:
- https://oeis.org/A002206
- https://oeis.org/A002207

These OEIS entries are background, not claimed identifiers for the new
threshold asymptotic or for the threshold sequence itself.

## Scope of the search

The arXiv record, full source, source bibliography, classical OEIS
records, and limited searches for the arXiv identifier and for Gregory
coefficient sign thresholds/asymptotics were examined. An arXiv search
for Gregory coefficients was also checked. Search-engine coverage was
noisy and often returned unrelated results. No later resolution of the
specific conjecture was found in those checks; this is not evidence of
exhaustive coverage, and it does not establish publication priority.

The modest finite inconsistency could reflect a typo or intended change
of starting order. Accordingly it is not treated as the main research
contribution. The proved e-based asymptotic would contradict an
all-sufficiently-large-order version as well.

No other source's full text is redistributed in this package. No external
submission, repository modification, or communication with the source
paper's authors was made.
