# Integration into ProveIt

This package is based on revision
cc34f73596336f2466d9754cb0f3635bd2bedade.
It is an independently reviewable continuation, not a change already made
to the repository.

## Suggested section placement

| New source | Suggested destination | Main dependency |
|---|---|---|
| sections/uniform_saddle.tex | After chapters/04-proportional-depth.tex | Positive harmonic-depth integral, rederived in the section |
| sections/reflected_moments.tex | After the reflected and sharp moment discussion in Chapter 8 | Classical gamma series; exact compact inequality certificate included |
| sections/lerch_bifurcations.tex | After chapters/09-zero-geometry.tex in Chapter 10 | Appell–Laplace zero bound, reproved in the section |
| sections/gaussian_candidate.tex | Following the S6 conjecture in chapters/04-cyclotomic-quotients.tex | Source S4 proof; new direct Euler bound |
| sections/verification_and_audit.tex | Validation supplement or condensed editorial notes | Included scripts and pinned source status |
| sections/further_research.tex | Research programme near chapters/10-discovery.tex | New theorem and conjecture labels |

All article-defined labels use the **cont26:** prefix to reduce collision risk.
The article's bibliography keys can be mapped to existing repository entries.
The sections require ordinary theorem environments and standard AMS notation;
the editorial article.tex supplies a complete standalone preamble.

## Source changes that should accompany integration

1. Apply or adapt **s6_evidence_status.patch**. It adds the later exact
   900-term residual certificate from the current validation ledger to the
   chapter's evidence paragraph. The identity remains a conjecture.
2. In the closing expanding-range discussion of the proportional-depth
   chapter, retain the warning about the compact-parameter theorem, then
   replace the open-problem sentence with a reference to the new
   **cont26:thm:uniform** and **cont26:eq:expanding-range**.
3. Preserve the fixed-m hypotheses of the older reflected moment and sharp
   remainder theorems. Add references to **cont26:joint:thm:laplace** and
   **cont26:joint:thm:critical** for the two new simultaneous-growth regimes.
   No theorem uniform over every exponent ratio is asserted.
4. Preserve the source's eventual large-derivative-order qualification for
   Lerch zero saturation. Add **cont26:cor:bif-kone** as a precise small-order
   limitation and **cont26:cor:bif-interior** for the forced transitions.
5. Keep **cont26:conj:s8** as a conjecture. The finite exact computation
   **cont26:prop:s6-s8-proximity** proves bounds, not equality.

The patch can be checked from a checkout of the pinned repository with:

    git apply --check /path/to/integration/s6_evidence_status.patch

It has not been applied to the remote repository. Later revisions may require
manual adjustment of the surrounding context.

## Evidence to retain with the mathematical text

Retain the full certificate generators and JSON proof objects, not merely the
replay receipt. The exact proof replay uses only Python's standard library.
The write-up supplies all convergence, tail, covering, and multiplicity
arguments that turn the finite calculations into mathematical conclusions.

The coefficient compiler and numerical diagnostics should be labeled separately.
Neither a successful floating-point check nor the rational proximity of the
Gaussian candidate is a symbolic period identity.

The original S4 theorem and its 911-row certificate are already present in
the pinned source. They are background for this continuation and should not
be duplicated as a newly proved result.

## Review priorities

The highest-value independent checks are the uniformity in all three harmonic
parameters, the reflected critical-window weighted tail estimates, the analytic
coverage of the 112 compact intervals, the no-escape argument for Lerch zeros,
and the normalization of the S8 vector. All have been checked during preparation;
the section proofs and scripts make another independent review possible.

Global priority has not been claimed. Bibliographic review can continue during
integration without changing the validity or explicit scope of the theorems.
