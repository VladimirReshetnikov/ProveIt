# Source and proof-boundary audit

Access and preparation date: 29 September 2026.
Pinned ProveIt commit: `afb2d1227d8bc5df3beffc1463e958db3544960b`.

## Repository sources inspected

### A290268 investigation notes

https://github.com/VladimirReshetnikov/ProveIt/blob/afb2d1227d8bc5df3beffc1463e958db3544960b/Oeis/A290268/README.md

This source supplies the exact coefficient model, the derivative/depth
bridge, the conjectured support and count, the symmetry holes, discussions
of depths 1 and 2, and the stated open core at higher depths and in the
general-k bulk. Its reported finite scans are background; they are not
used as certificates for this article.

### Actual support-to-count module

https://github.com/VladimirReshetnikov/ProveIt/blob/afb2d1227d8bc5df3beffc1463e958db3544960b/Combinatorics/DerivativeExpansions/A290268/Lean/A290268/Main.lean

The actual declarations consume support equality, or the two support
inclusions, as hypotheses. This article does not misread the conditional
reduction as an unconditional proof of the OEIS formula.

### Scoped directory inspection

https://github.com/VladimirReshetnikov/ProveIt/tree/afb2d1227d8bc5df3beffc1463e958db3544960b/Combinatorics/DerivativeExpansions/A290268/Lean/A290268

The returned directory tree contains Core, ClosedForm, Count, Structural,
Table, and Main. Other module names discussed in the investigation README
were not present in this scoped listing. Their names or descriptions are
not treated as kernel-certification evidence. No full repository rebuild
or Lean axiom audit was performed for this article.

## External primary sources

1. OEIS A290268: https://oeis.org/A290268
   The inspected entry describes the derivative term-count sequence and
   labels the rational generating function conjectural. The article uses
   that status as the starting point, not as proof that no unpublished
   solution exists.
2. NIST DLMF, equation 18.23.7: https://dlmf.nist.gov/18.23.E7
   Classical Meixner-Pollaczek generating function. The article derives all
   polynomial identities it needs, while identifying the classical family.
3. F. Stampach, *Asymptotic behavior and zeros of the Bernoulli polynomials
   of the second kind*, Journal of Approximation Theory 262 (2021), 105517.
   Preprint: https://arxiv.org/abs/2011.13808
   PDF: https://arxiv.org/pdf/2011.13808
   Integer interlacing is in a different parameter regime. It does not
   supply the higher-depth theorem proved in this article.
4. The bibliographic volume/article number in item 3 was independently
   cross-checked against the primary paper by R. B. Paris:
   https://arxiv.org/html/2105.00686v1
   This is bibliographic verification, not an additional mathematical
   dependency of the article.

## Novelty boundary

The targeted repository and literature checks did not locate a prior proof
of the all-depth bulk theorem, the explicit fixed-depth finite reduction,
or the completed depth-three and depth-four statements in this form.
These checks are not a comprehensive historical-priority search. Claims of
continuation are relative to the inspected A290268 material. Classical
reflection, orthogonal-polynomial, contour, covariance, and Chebyshev-system
arguments are not claimed as inventions.

## Proof and computation boundary

Conventional proofs establish the coefficient bridge, centered factorization,
bulk positivity, symmetry holes, branch-cut representation, likelihood-ratio
comparisons, fixed-depth finite bounds, small-certificate criterion, and
Mellin zero bound. The depth-three/four completion then requires exactly
specified finite rectangles and six seed signs. These are verified by
executed arbitrary-precision integer code. Two independent recurrences
agree on every rectangle entry. The modular residues are reproducible
nonzero witnesses, not claims of a formally verified checker.

The full counting conjecture over unbounded depth is not established.
No Lean or Rocq source is delivered or claimed to have been tested. No
external referee or independent human review is claimed. Source URLs are
pinned when possible; all generated verification data can be rebuilt from
the included code without network access.
