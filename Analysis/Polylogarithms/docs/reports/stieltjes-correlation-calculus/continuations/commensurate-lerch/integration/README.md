# Suggested integration into ProveIt

This delivery is a research package, not an applied repository patch. The
canonical source anchor is commit
`338a3a3877c337f981072061c16bc8ee1d87155d`.

## Placement and dependencies

Preserve the archive under the repository's incoming/intake procedure, then
integrate the proved material near the reciprocal Lerch/Hurwitz integral
material in the Hurwitz–Stieltjes volume. The dependencies are standard
Lerch continuation, Gamma reflection, weighted convolution/Fourier inversion,
finite Laurent expansions, and the Stieltjes Laurent convention.

The sections are modular. All labels begin `clc:`. Do not copy the standalone
preamble into the canonical preamble unchanged: adapt generic macros such as
`\CC`, `\C`, `\R`, `\bs`, and the theorem environments to the book's existing
notation, or rename the new macros with a private prefix. Preserve the
normalization and domains before shortening proofs.

## Status updates justified by this package

The preceding **Reciprocal Lerch Convolutions** report's further-research
question 5 (commensurate dilations) is answered here by finite closure for
all complex aligned orders, not only positive integer orders. Its question 2
(unequal-shift independent-order expansion) is answered by a normally convergent
series in one common center, throughout the stated common-strip domain. The
original equal-scale right-half-plane shift domain is fully covered.

This does not justify marking every unrelated all-order or same-direction
Mellin question solved. It does not resolve the full compact multivariate tilt
problem, nor the canonical Gaussian S6 or revised S8 relation vectors.

## Nonnegotiable safeguards

1. Use `q**(-s) * F_{1+A/q,s}(exp(q*x))`; the raw unequal-scale profiles do not
   satisfy pure order addition. The theorem concerns a common affine center A.
2. Retain `E_a(v)=v*zeta(v+1,a)` with `E_a(0)=1`, and combine simple Hurwitz poles
   into differences. Do not zero a Pochhammer factor next to a pole.
3. Keep the combined positive-mu Lerch continuation. The proof establishes
   cancellation of the jump, not arbitrary independent branch choices.
4. State the common weighted strip for unequal centers. Individual profile
   admissibility alone is not substituted for it.
5. Distinguish the finite inner closure from the generally infinite, normally
   convergent unequal-center expansion.
6. Retain the restricted scopes of the two rigidity theorems; neither asserts
   arithmetic independence or unrestricted special-function nonreducibility.

The source audit lists incoming archives whose names were visible but whose
binary contents were not read. Integration should reconcile those archives
before assigning priority or eliminating apparent duplicates.
