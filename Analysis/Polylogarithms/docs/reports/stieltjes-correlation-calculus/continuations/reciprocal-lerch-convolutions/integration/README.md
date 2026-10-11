# Integration guide

## Suggested destination

A natural additive path is:

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/mellin-lerch-dilation/continuations/reciprocal-lerch-convolutions/`

The maintainer may choose a dedicated report path instead. Preserve the complete
article and its check results. No patch against a moving manuscript is imposed.

## Minimal manuscript addition

`manuscript_insert.tex` is an alternative short insertion, not something to add
on top of a wholesale copy of every article section. It summarizes the
reciprocal theorem, its all-order Stieltjes law, and logarithmic moments with
a concise analytic proof. `insert_preview.tex` is its standalone driver.
All insertion labels begin with `rlc:insert:`. Full-article labels begin with
`rlc:`. The short insertion does not require a new bibliography key.

## Status wording

Suggested research-question update:

> The reciprocal-argument companion of the product Mellin problem admits an
> entire-order finite closure at every multiplicative depth. Its full
> polynomial logarithmic-moment calculus, ordinary Stieltjes products, and
> integral-shift harmonic collapses are proved in *Reciprocal Lerch
> Convolutions*. This does not settle the full same-direction two-scale
> arbitrary-order problem.

Suggested compatibility-question update:

> In the reciprocal family, the derivative/primitive algebra is explicit:
> [partial_a,D_a]=I and [partial_a,J_a]=-J_a^2. Rising-factorial derivatives
> use elementary harmonic polynomials, while consecutive-shift reductions
> use complete homogeneous harmonic polynomials. This is a proved compatible
> instance, not a claim of a universal merger of all existing calculi.

Retain S4 as already proved. Keep the canonical S6 and revised S8 environments
conjectural. Do not label failed numerical searches as independence proofs.
Do not label the floating-point diagnostics as interval certificates.

## Review order

Read the weighted holomorphy proof, the bilateral transform, all-depth order
addition, central-factorial recurrence, and full moment-reduction theorem.
Then review the Stieltjes specializations and the unequal-shift arithmetic
collapses. Run the 336 exact assertions and the 91 numerical diagnostics.
The three negative controls must be rejected.

Before a global novelty claim, compare the statement index with the three
uninspected incoming archives named in `SOURCE_AUDIT.md`.
