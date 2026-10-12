# Proposed integration

## Source snapshot and placement

Source revision: **e3d7ec5d3f9be259c1f91edaea4389f4e79b5b03**, inspected 11 October 2026.

Keep this contribution together as a new report before any selective insertion. One suitable proposed directory is:

Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/ordered-boundary-gamma-kernels/

The repository maintainer can choose the final placement during intake. No existing report needs to be overwritten.

| Article sections | Natural dependency / destination | Main integration point |
|---|---|---|
| 2–4 | Incoming Finite-Difference Determinants, after polarization | Ordered labels, exact two-shift kernel, continuation and digamma master |
| 5 | Finite-difference cutoff generator branch | All-complex-order disk identity and (1-z)^2 depth-two cancellation |
| 6 | Hurwitz and Stieltjes calculus | Ordinary subtracted jets, beta–Stieltjes transform, declared finite-part coordinate |
| 7 | Finite-difference structural continuation | Exact chamber transport and finite collision-block compiler |
| 8 | harmonic-tail-gamma, following gap:complementary | Gamma basis, exact normalization, fixed-gap eventual theorem and harmonic correction |
| 9 | Research/status ledger | Precise remaining scope and proposed next questions |

## Proposed status wording

**Ordered mixed sums.** The two-particle ordered mixed-order/mixed-shift sum now has an exact one-index reduction on Re(t)>1, Re(s+t)>0, with right-half-plane shifts. Its joint meromorphic continuation, complete polar coefficient list, positive integer evaluations, and digamma generating master are supplied with proofs.

**Noninteger cutoff generators.** A finite expression on |z|<1 is supplied in ordinary polylogarithms, one depth-two polylogarithm, and beta–Lerch transforms. It is entire in the two orders. Its endpoint is governed by the original convergence domain, with separated divergences kept in their proved combination.

**All-rank ordered localization.** Critical finite differences give an explicit finite block formula with at most floor((r+1)/2) free indices; anchored sectors improve that count. This is a representation theorem, not a claim of arithmetic minimal depth.

**Unequal harmonic-tail reconstruction.** For every fixed integer m>=1, all sufficiently large pairs (p,q)=(2b-2m,2b) have optimal first-q formal moment prefix. The proof constructs a Gamma integral basis, evaluates its nonzero initial determinant, and derives a nonzero signed Vandermonde asymptotic with an explicit harmonic correction. No numerical threshold is supplied; the full unequal-even and full gap-six assertions remain open here.

## Inherited results and non-claims

- The existing harmonic-tail-gamma report supplies the exact fixed-gap recurrence bridge. Section 8 reproduces its normalization, using half-orders as the subscripts of M.
- Quartic Spectral Reconstruction supplies the earlier eventual theorem with smaller order fixed.
- Bilinear Tails and Determinants and Tail Kernels and Boundary Products already supply smaller-order-ten completion. The latter's Sections 6–7 supply complete smaller-order-ten and smaller-order-twelve theorems. Retain those attributions.
- The Gaussian S6 and revised S8 period identities remain conjectural. The old rejected S8 vector is an already recorded source correction.
- Formal coordinate rank does not establish arithmetic independence.
- A hard-cutoff constant differs from the fixed-coordinate Laurent finite part by the boundary correction proved in the article.
- The all-rank sector series are individually proved first in the stronger expanded-convergence domain. Their continuation beyond it is collective.
- Internal independent derivation checks and executable diagnostics are included. External peer review and formal proof verification are not claimed.

## Proposed README correction

The patch remove_duplicate_readme_paragraph.patch removes only the second consecutive copy of the manuscript README paragraph concerning the complete 1,032-input first-letter-X family, its rank 1,008, and its kernel dimension 24.

The patch passes git apply --check at the pinned revision. It has not been applied to the source repository. It changes no mathematical claim.

## Dependencies to retain in any extracted theorem

For the ordered formula, retain the second-difference normalization 1/2, the asymmetric convergence domain, and the combined interpretation of the kernel difference.

For the Gamma theorem, retain the omitted binomial-index-zero convention, the subtraction of the derivative at zero, the positive diagonal factors in the complementary-minor identity, the even-mode phase cancellation, and the fixed-gap qualification. Removing any of these can change the statement or its normalization.

For the Stieltjes formulas, retain the convention zeta(1+u,a)=1/u+sum((-1)^m gamma_m(a)u^m/m!) and subtract inside each defining series before differentiating.
